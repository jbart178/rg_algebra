theory No_Translate
  imports
    "Main"
    "../General/Relations"
    "HOL-Hoare_Parallel.Quote_Antiquote"

begin

text \<open>We use (\<lpred>p\<rpred>) to give a relation where (\<sigma>,\<sigma>') satisfy predicate p\<close>

syntax
  "_rel" :: "(('a*'a) \<Rightarrow> bool) \<Rightarrow> 'a rel" ("\<lpred>_\<rpred>" [0] 1000)
  "_set" :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" ("\<lrel>_\<rrel>" [0] 1000)
  "_comp" :: "[('b * 'c) set, ('a * 'b) set] \<Rightarrow> ('a * 'c) set" (infixr "\<Zsemi>" 75)

translations
  "\<lpred> p \<rpred>" \<rightharpoonup> "CONST Collect(_quote p)"
  "\<lrel> p \<rrel>" \<rightharpoonup> "CONST Collect(_quote p)"
  "r \<Zsemi> s" \<rightharpoonup> "r O s"

lemma strengthen_pre: "(\<lpred>p1\<rpred> \<subseteq> \<lpred>p2\<rpred>) \<equiv> p1 \<Longrightarrow> p2"
  by blast

lemma dom_restrict: "(\<lrel>p\<rrel> \<triangleleft> \<lpred>q2\<rpred> \<subseteq> \<lpred>q1\<rpred>) \<equiv> p \<and> q2 \<Longrightarrow> q1"
  by (smt (verit, del_insts) IntE IntI case_prodE case_prodI2 mem_Collect_eq restrict_domain_def subsetI subset_empty)

lemma range_restrict: "(\<lpred>q2\<rpred> \<triangleright> \<lrel>p\<rrel> \<subseteq> \<lpred>q1\<rpred>) \<equiv> p \<and> q2 \<Longrightarrow> q1"
  by (smt (verit, ccfv_threshold) Collect_empty_eq IntI case_prodE case_prodI inf_le2 mem_Collect_eq range_restrict_remove restrict_range_def subsetD)


 
  

lemma id_rel: "Id \<equiv> \<lpred>x = x'\<rpred>"
  by sledgehammer

end