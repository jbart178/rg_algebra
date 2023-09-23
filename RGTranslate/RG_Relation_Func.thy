theory RG_Relation_Func
  imports Main
begin

text \<open> 
Contains the syntax and translations for relations using
the function representation 
\<close>

ML_file \<open>utils.ML\<close>

section \<open>Variable transformation\<close>

ML \<open>

fun wrap_free_vars prime_wrapper non_prime_wrapper trm =
  let
    fun wrap_free_vars_helper prime_wrapper non_prime_wrapper trm ptypes nptypes = 
      case trm of 
          x $ Free("<markup>", _) => wrap_free_vars_helper 
                prime_wrapper non_prime_wrapper x ptypes nptypes
        | (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ u $ _) => wrap_free_vars_helper 
                prime_wrapper non_prime_wrapper u ptypes nptypes
        | (Const (\<^syntax_const>\<open>_constrainAbs\<close>, _) $ u $ _) =>  wrap_free_vars_helper 
                prime_wrapper non_prime_wrapper u ptypes nptypes
        | u $ u' =>
          let 
            val (lhs, ptypes', nptypes') =  
                wrap_free_vars_helper prime_wrapper non_prime_wrapper u ptypes nptypes
            val (rhs, ptypes'', nptypes'') =  
                wrap_free_vars_helper prime_wrapper non_prime_wrapper u' ptypes nptypes
            (*val _ = @{print} {lhs=lhs, rhs=rhs}*)
          in (lhs $ rhs, List.concat [ptypes', ptypes''],  List.concat [nptypes', nptypes'']) end
        | Free(s, t) => 
          let
            (*val _ = @{print} trm*)
            val ignore_pattern = "_ig"
            val should_ignore = if String.isSuffix ignore_pattern s then true else false
            val trimmed_name = 
              if String.isSuffix ignore_pattern s then 
                String.substring(s, 0, (String.size s) - (String.size ignore_pattern)) 
              else s;
            val is_prime = if String.isSuffix "'" trimmed_name then true else false
          in
            if should_ignore then (Free(trimmed_name,t), ptypes, nptypes)
            else if s = "<markup>" then (Free(trimmed_name,t), ptypes, nptypes)
            else if is_prime then
              let
                (* Remove the ' from the name and wrap it *)
                val updated_name = String.substring(trimmed_name, 0, (String.size trimmed_name) - 1);
              in 
                (prime_wrapper $ Free(updated_name, t), ptypes, t :: nptypes)
              end
            else 
              (non_prime_wrapper $ Free(trimmed_name, t), t :: ptypes, nptypes)
          end
      | Abs(s, t, u) => 
          let
            val (res, ptypes', nptypes') = wrap_free_vars_helper 
                prime_wrapper non_prime_wrapper u ptypes nptypes
          in (Abs(s, t, res), ptypes', nptypes') end
      | _ => (trm, ptypes, nptypes)
  in wrap_free_vars_helper prime_wrapper non_prime_wrapper trm [] [] end
\<close>

section \<open>Syntax with translation\<close>

ML \<open>
fun rgrelation_tr ctxt ts =
  let
    val trm = hd ts
    val _ = @{print} trm
    val max_bound = RG_Utils.max_bound_var trm
    val (wrapped_vars, ptypes, nptypes) = wrap_free_vars (Bound (max_bound + 1)) (Bound (max_bound + 2)) trm
    val _ = @{print} {trm=trm, wrapped=wrapped_vars, p=ptypes, np=nptypes}
    val s'_abs_typ = Type ("fun", List.concat [[TFree ("'a", ["HOL.type"])], ptypes])
    val s_abs_typ = Type ("fun", List.concat [[TFree ("'a", ["HOL.type"])], nptypes])
    val ((s, s_trm), ctxt') = Variable.dest_abs (Abs("s", s_abs_typ, wrapped_vars)) ctxt
    val ((s', _), _) = Variable.dest_abs (Abs("s'", s'_abs_typ, s_trm)) ctxt'
    val s'_abs_term = Abs (fst s', snd s, wrapped_vars)
    val s_abs_term = Abs (fst s, snd s', s'_abs_term)
    
    val product_term = HOLogic.mk_case_prod s_abs_term
    val set_collection = HOLogic.Collect_const (HOLogic.mk_prodT (snd s', snd s))

    val translation = set_collection $ product_term  
 val _ = @{print} translation
  in translation end
\<close>

syntax "_rgrelation" :: "args => 'a set"  ("\<lrel>_\<rrel>")

parse_translation \<open>[(@{syntax_const "_rgrelation"}, rgrelation_tr)]\<close>

section \<open>Testing\<close>

text \<open> Test a basic expression \<close>
lemma "\<lrel> x > x' \<rrel> = {(s, s'). s x > s' x}"
  by (rule refl)

text \<open> Test an expression with multiple variables \<close>
lemma "\<lrel> x > y' \<rrel> = {(s, s'). s x > s' y}"
  by (rule refl)

text \<open> Test an expression containing quantifiers \<close>
lemma "\<lrel> \<forall>x. x > y' \<rrel> = {(s, s'). \<forall>x. x > s' y}"
  by (rule refl)

text \<open> Test the translation function directly with fully formed expressions \<close>
ML \<open>
@{term "{(s, s'). s x > s' x}"};
val _ = RG_Debug.print_term @{context} (rgrelation_tr @{context} [@{term "x > x'"}])
val _ = RG_Debug.print_term @{context} (rgrelation_tr @{context} [@{term "x > y'"}])
val _ = RG_Debug.print_term @{context} (rgrelation_tr @{context} [@{term " \<forall>x. x > y'"}])
val _ = RG_Debug.print_term @{context} (rgrelation_tr @{context} [@{term "(x::nat) > x' \<and> (y::bool) = y'"}])
\<close>
end