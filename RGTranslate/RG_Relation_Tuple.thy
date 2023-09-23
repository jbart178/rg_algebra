theory RG_Relation_Tuple
  imports Main
begin

text \<open> 
Contains the syntax and translations for relations
using the tuple representation
\<close>

ML_file \<open>utils.ML\<close>


section \<open>Variables within the theory context\<close>

ML \<open>
signature RG_VAR_LIST =
sig
  val get: theory -> term list
  val add: term -> theory -> theory
  val reset: theory -> theory
end;

structure RG_Var_List: RG_VAR_LIST =
struct

structure Data = Theory_Data
(
  type T = term list;
  val empty = [];
  val extend = I;
  val merge = Library.merge (op aconv);
);

val get = Data.get;

fun add t thy = Data.map (cons (Sign.cert_term thy t)) thy

val reset = Data.put [];

end;
\<close>

section \<open>Variable Transformations\<close>

ML \<open>

(* Builds up a list [(trm, idx)] which maps terms to de Bruijn indices *)
fun generate_bound_mapping [] start = ([], start)
  | generate_bound_mapping (x :: xs) start =
    let
      val (mapped, start') = generate_bound_mapping xs (start + 1)
    in 
      ((x, start) :: mapped, start')
    end;

(* Returns the de Bruijn index of a given term *)
fun lookup_bound _ [] = ~1
  | lookup_bound name ((Free(s, _), idx) :: xs) =
    if s <= name andalso s >= name then idx else lookup_bound name xs
  | lookup_bound _ _ = raise Fail "Bad lookup";

(* Generates a list of terms where the names are suffixed with primes *)
fun generate_prime_list [] = []
  | generate_prime_list (Free(str, typ) :: ts) = 
    let
      val new_trm = Free(str ^ "'", typ)
    in 
      new_trm :: generate_prime_list ts
    end
  | generate_prime_list _ = raise Fail "Bad variable list";

(* Replaces the Free variables in the given term with their Bound counterparts *)
fun replace_bound_vars trm mapping =
  case trm of
      Free(s, t) => 
        let
          val idx = lookup_bound s mapping
        in
          if idx < 0 then Free(s, t) else Bound(idx)
        end
    | Abs (s, t, u) => Abs(s, t, replace_bound_vars u mapping)
    | u $ u' => (replace_bound_vars u mapping) $ (replace_bound_vars u' mapping)
    | _ => trm

(* Wraps a term with Abs terms using a given bound mapping *)
fun wrap_abs trm [] = trm
  | wrap_abs trm ((Free (s,t), _) :: xs) = Abs (s, t, wrap_abs trm xs)
  | wrap_abs _ _ = raise Fail "Bad variable list"
\<close>

section \<open>Syntax with translation\<close>

ML \<open>
fun rgrelation_tr ctxt ts =
    let
      (* Get the information from the context *)
val _ = @{print} ts
      val trm = hd ts
      val _ = @{print} trm
      val var_list = RG_Var_List.get (Proof_Context.theory_of ctxt)
      val prime_list = generate_prime_list var_list
      val _ = @{print} {var_list = var_list, prime_list = prime_list}

      (* Figure out the bound indices we'll need *)
      val start_bound = (RG_Utils.max_bound_var trm) + 1        
      val (non_prime_map, next_bound) = generate_bound_mapping var_list start_bound
      val (prime_map, _) = generate_bound_mapping prime_list next_bound
      val _ = @{print} {non_prime = non_prime_map, prime = prime_map}
      
      (* Update our mapping to have the correct typing information *)

      (* Replace the Free variables with their bound counterparts *)
      val trm' = replace_bound_vars trm non_prime_map
val _ = @{print} trm'
      val trm'' = replace_bound_vars trm' prime_map 
val _ = @{print} trm''

      (* Wrap the primes in their Abs terms *)
      val trm''' = wrap_abs trm'' (rev prime_map)
val _ = @{print} trm'''
      val trm'''' = HOLogic.mk_case_prod trm'''
val _ = @{print} trm''''
      val trm''''' = wrap_abs trm'''' (rev non_prime_map)
val _ = @{print} trm'''''
      val trm'''''' =  HOLogic.mk_case_prod trm'''''
(*
      val _ = RG_Debug.print_term ctxt trm   
      val _ = RG_Debug.print_term ctxt trm'    
      val _ = RG_Debug.print_term ctxt trm''  
      val _ = RG_Debug.print_term ctxt trm'''
*)
      val _ = @{print} {
          orig = trm, 
          bound_nonprime = trm', 
          bound_prime = trm'', 
          abs_prime = trm''',
          vars = var_list,
          t1 = trm'''',
          t2 = trm''''',
          t3 = trm''''''
          } 
     (*
      val dummy = @{term "{((x, y), (x', y')). x > x'}"}
      val _ = @{print} dummy*)
    in trm'''''' end
\<close>

syntax "_rgrelation" :: "args \<Rightarrow> 'a set"  ("\<lrel>_\<rrel>" [0] 1000)

parse_translation \<open>[(\<^syntax_const>\<open>_rgrelation\<close>, rgrelation_tr)]\<close>

section \<open>Testing\<close>

text \<open>Test a single variable \<close>
setup \<open>
  RG_Var_List.add (@{term "x"})
\<close>

lemma "\<lrel> x < x' \<rrel> = {(x, x'). x < x'}"
  by (rule refl)

setup \<open>
  RG_Var_List.reset
\<close>

text \<open>Test a pair of variables \<close>
setup \<open>
  RG_Var_List.add (@{term "x"}) #>
  RG_Var_List.add (@{term "y"})
\<close>

lemma "\<lrel> x > x' \<rrel> = {((x,y), (x',y')). x > x'}"
  by (rule refl)

setup \<open>
  RG_Var_List.reset
\<close>

text \<open>Test an odd number of variables \<close>
setup \<open>
  RG_Var_List.add (@{term "x"}) #>
  RG_Var_List.add (@{term "y"}) #>
  RG_Var_List.add (@{term "z"})
\<close>

lemma "\<lrel> x > x' \<rrel> = {((x, y, z), (x', y', z')). x > x'}"
  by (rule refl)

setup \<open>
  RG_Var_List.reset
\<close>

setup \<open>
  RG_Var_List.add (@{term "x"}) #>
  RG_Var_List.add (@{term "y"})
\<close>

ML \<open>
val trm = rgrelation_tr @{context} [@{term "x > x'"}]
\<close>

setup \<open>
  RG_Var_List.reset
\<close>


end
