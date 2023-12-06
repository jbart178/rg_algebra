theory With_Hoare
  imports 
    "../Programming/IntroPar_Big"
    "../Programming/State_Relations"
    "../Programming/Assignments"
"HOL-Hoare_Parallel.RG_Syntax"
begin

text \<open>Quote Antiquote code syntax is introduced from Quote_Antiquote theory with notation edit\<close>
syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)
  "_Assert"    :: "'a \<Rightarrow> 'a set"                    ("(\<lpred>_\<rpred>)" [0] 1000)

translations
  "\<lpred>b\<rpred>" \<rightharpoonup> "CONST Collect \<guillemotleft>b\<guillemotright>"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr \<^syntax_const>\<open>_antiquote\<close> t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(\<^syntax_const>\<open>_quote\<close>, K quote_tr)] end
\<close>

text \<open>More code from RG_Syntax\<close>
syntax
  "_before" :: "id \<Rightarrow> 'a" ("\<ordmasculine>_")
  "_after"  :: "id \<Rightarrow> 'a" ("\<ordfeminine>_")

translations
  "\<ordmasculine>x" \<rightleftharpoons> "x \<acute>CONST fst"
  "\<ordfeminine>x" \<rightleftharpoons> "x \<acute>CONST snd"


locale ctxt = strong_spec + intro_par_big + state_relations + expressions + assignments
begin

lemma
  assumes "\<forall> s. r1 s \<longrightarrow> r2 s"
  shows "rely \<lpred>r1 \<acute>s\<rpred> \<ge> rely \<lpred>r2 \<acute>s\<rpred>"
  by (metis Collect_mono assms guar_rely_refine_rely)

lemma 
  shows "\<lparr>\<lpred>\<ordfeminine>x \<subseteq> \<ordmasculine>x\<rpred>\<rparr> \<ge> \<lparr>\<lpred>\<ordfeminine>x \<subset> \<ordmasculine>x\<rpred>\<rparr>"
  by (simp add: Collect_mono_iff psubset_eq spec_strengthen)


lemma
" (\<lbrace>\<lpred> n < length \<acute>A \<rpred>\<rbrace>;\<lparr>\<lpred>\<ordfeminine>A ! i = 0\<rpred>\<rparr>) \<iinter>
     (rely \<lpred> length \<ordmasculine>A = length \<ordfeminine>A \<and> \<ordmasculine>A ! i = \<ordfeminine>A ! i \<rpred>) \<iinter>
     (guar \<lpred> length \<ordmasculine>A = length \<ordfeminine>A \<and> (\<forall>j<n. i \<noteq> j \<longrightarrow> \<ordmasculine>A ! j = \<ordfeminine>A ! j) \<rpred>)
    
 \<ge> (\<lbrace>\<lpred> n < length \<acute>A \<rpred>\<rbrace>;\<lparr>\<lpred>\<forall>i < n. \<ordfeminine>A ! i = 0\<rpred>\<rparr> \<iinter> (rely \<lpred> \<ordmasculine>A = \<ordfeminine>A \<rpred>) \<iinter> (guar \<lpred>True\<rpred>))"
  by sledgehammer

lemma
  shows "(rely \<lpred>r s\<rpred>) \<iinter> \<lparr>\<lpred>q1 s \<and> q2 s\<rpred>\<rparr> \<ge> ((rely \<lpred>r s \<or> r1 s\<rpred>) \<iinter> (guar \<lpred>r2 s\<rpred>) \<iinter> \<lparr>\<lpred>q1 s\<rpred>\<rparr>) \<parallel> ((rely \<lpred>r s \<or> r2 s\<rpred>) \<iinter> (guar \<lpred>r1 s\<rpred>) \<iinter> \<lparr>\<lpred>q2 s\<rpred>\<rparr>)"
  sorry

end

end 