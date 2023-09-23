theory Sample_Translation
  imports Main
begin

text \<open> 
Contains the sample translation provided in the thesis paper
\<close>

section \<open>Syntax with translation\<close>

ML \<open>
fun replace_free_x trm =
  case trm of
      Free(s, t) => if s = "x" then Free("y", t) else Free(s, t)
    | Abs (s, t, u) => Abs(s, t, replace_free_x u)
    | u $ u' => (replace_free_x u) $ (replace_free_x u')
    | _ => trm

fun sample_tr ctxt [args] = replace_free_x args
\<close>

syntax "_sample" :: "args => 'a"  ("\<lpred>_\<rpred>")

parse_translation \<open>[(\<^syntax_const>\<open>_sample\<close>, sample_tr)]\<close>

section \<open>Testing\<close>

lemma "\<lpred>x > a \<and> x > b\<rpred> \<equiv> y > a \<and> y > b"
  by (simp)

end