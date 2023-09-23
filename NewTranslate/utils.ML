(* utils.ML
   
   Contains useful utility functions and shared functionality
*)

(* Used to control debugging functions such as verbose type printing *)
(* Set to false to disable debugging functionality *)
val RG_DEBUG = true

(* Pretty printer switching functionality *)
local
fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
fun pp_list xs = Pretty.list "[" "]" xs
fun pp_str s = Pretty.str s
fun pp_qstr s = Pretty.quote (pp_str s)
fun pp_int i = pp_str (string_of_int i)
fun pp_sort S = pp_list (map pp_qstr S)
fun pp_constr a args = Pretty.block [pp_str a, Pretty.brk 1, args]
in
fun raw_pp_typ (TVar ((a, i), S)) =
pp_constr "TVar" (pp_pair (pp_pair (pp_qstr a, pp_int i), pp_sort S))
| raw_pp_typ (TFree (a, S)) =
pp_constr "TFree" (pp_pair (pp_qstr a, pp_sort S))
| raw_pp_typ (Type (a, tys)) =
pp_constr "Type" (pp_pair (pp_qstr a, pp_list (map raw_pp_typ tys)))
end;

fun set_verbose_pretty_printer _ = 
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ);

fun set_default_pretty_printer _ = 
  ML_system_pp (fn depth => fn _ => 
    ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_typ Theory.get_pure);

if RG_DEBUG then set_verbose_pretty_printer () else set_default_pretty_printer ();

(* Debugging utility methods *)
signature RG_DEBUG = 
sig
  val print_term: Proof.context -> term -> unit
  val print_type: Proof.context -> typ -> unit
end;

(* General utility methods *)
signature RG_UTILS = 
sig
  val max: int -> int -> int
  val max_bound_var: term -> int
end;

(* Utility method implementations *)
structure RG_Debug: RG_DEBUG =
struct
  fun print_term ctxt trm = Pretty.writeln (Syntax.pretty_term ctxt trm)
  fun print_type ctxt typ = Pretty.writeln (Syntax.pretty_typ ctxt typ)
end;

structure RG_Utils: RG_UTILS =
struct

fun max x y = if x > y then x else y

(* Returns the highest bound variable in a given term.
   If no bound variables are present returns -1, this allows
   us to simply add 1 when doing wrapping. This method is used
   whenever you need to get a bound index that won't clash with
   a given term
*)
fun max_bound_var (Bound (x:int)) = x
  | max_bound_var (Abs (_, _, u)) = max_bound_var u
  | max_bound_var (u $ u') = max (max_bound_var u) (max_bound_var u')
  | max_bound_var _ = ~1
end;