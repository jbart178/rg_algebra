theory No_Translate
  imports
    "Main"
    "../General/Relations"
    "HOL-Hoare_Parallel.Quote_Antiquote"
    "HOL-Examples.Records"
    "../Programming/State_Relations"
    "../Programming/Specification"
    "../General/Sequential"
begin

text \<open>We use (\<lpred>p\<rpred>) to give a relation where (\<sigma>,\<sigma>') satisfy predicate p\<close>
(*
syntax
  "_rel" :: "(('a*'a) \<Rightarrow> bool) \<Rightarrow> 'a rel" ("\<lpred>_\<rpred>" [0] 1000)
  "_set" :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" ("\<lrel>_\<rrel>" [0] 1000)
  "_comp" :: "[('b * 'c) set, ('a * 'b) set] \<Rightarrow> ('a * 'c) set" (infixr "\<Zsemi>" 75)

translations
  "\<lpred> r \<rpred>" \<rightharpoonup> "CONST Collect(_quote r)"
  "\<lrel> p \<rrel>" \<rightharpoonup> "CONST Collect(_quote p)"
  "r \<Zsemi> s" \<rightharpoonup> "r O s"
*)
definition relation :: "(('a*'a) \<Rightarrow> bool) \<Rightarrow> 'a rel" ("\<lpred>_\<rpred>" [30])
  where "relation r \<equiv> {(s, s') \<in> UNIV. r (s, s')} "

definition predset :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" ("\<lrel>_\<rrel>" [30])
  where "predset p = Collect(p)"

(* Set containing \<dots>*)
definition dunno :: "('a*'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a set" ("_\<bar>_\<bar>" [30,30])
  where "dunno r p \<equiv> {s'. (\<exists> s. p s \<and> r (s,s'))}"

lemma strengthen_pre: "(\<lrel>p1\<rrel> \<subseteq> \<lrel>p2\<rrel>) \<Longrightarrow> (\<And>s. p1 s \<Longrightarrow> p2 s)"
  by (simp add: Collect_mono_iff predset_def)

lemma dom_restrict: "(\<lrel>p\<rrel> \<triangleleft> \<lpred>q2\<rpred> \<subseteq> \<lpred>q1\<rpred>) \<Longrightarrow> (\<And>s. p (fst s) \<and> q2 s \<Longrightarrow> q1 s)"
  by (smt (verit) Int_def UNIV_def in_mono mem_Collect_eq predset_def prod.collapse relation_def restrict_domain_def split_conv)

lemma range_restrict: "(\<lpred>q2\<rpred> \<triangleright> \<lrel>p\<rrel> \<subseteq> \<lpred>q1\<rpred>) \<Longrightarrow> (\<And>s. p (snd s) \<and> q2 s \<Longrightarrow> q1 s)"
  by (smt (verit, del_insts) IntI in_mono mem_Collect_eq predset_def prod.collapse relation_def restrict_range_def split_def top_greatest)

lemma "(Range (\<lrel>p\<rrel> \<triangleleft> \<lpred>r\<rpred>)) \<subseteq> (r\<bar>p\<bar>)"
  by (smt (verit, best) IntE RangeE dunno_def mem_Collect_eq predset_def relation_def restrict_domain_def split_conv subsetI)

lemma "(r\<bar>p\<bar>) \<subseteq> (Range (\<lrel>p\<rrel> \<triangleleft> \<lpred>r\<rpred>))"
  by (smt (verit, ccfv_threshold) Int_iff Int_iff Range.intros Range.intros Range_mono UNIV_def case_prodE case_prod_conv case_prod_unfold domain_restrict_remove dunno_def in_mono inf.orderE mem_Collect_eq mem_Collect_eq mem_Collect_eq predset_def prod.collapse prod.collapse prod.inject prod.inject relation_def restrict_domain_def subsetD subsetI)



record 'a vars =
  x :: nat
  \<dots> :: 'a

(*
definition id_rel :: "('a*'a) \<Rightarrow> bool" where
"id_rel s \<equiv> (fst s = snd s)"

lemma "Id = \<lpred>id_rel\<rpred>"
  by (metis (mono_tags, lifting) Collect_cong Id_fstsnd_eq UNIV_I id_rel_def prod.collapse relation_def split_def)
*)

(*
function id_rel_param :: "'b list \<Rightarrow> ('a vars * 'a vars) \<Rightarrow> bool" where
"id_rel_param (p#ps) s = id_rel_param ps ( s\<lparr>p := ( p (fst s) )\<rparr> ) " | 
"id_rel_param [] s = id_rel s"
*)

context state_relations
begin
definition id_rel :: "('state*'state) \<Rightarrow> bool" where
"id_rel s \<equiv> \<forall>x. ((get_var x (fst s)) = (get_var x (snd s)))"

definition id_rel_bar :: "'varname fset \<Rightarrow> ('state*'state) \<Rightarrow> bool" where
"id_rel_bar xs s \<equiv> \<forall>x :: 'varname. x|\<notin>|xs \<longrightarrow> ((get_var x (fst s)) = (get_var x (snd s)))"

lemma "\<lpred>id_rel\<rpred> \<subseteq> id_bar xs"
  by (smt (verit, ccfv_SIG) fst_conv id_rel_def mem_Collect_eq relation_def snd_conv split_conv state_relations.id_bar_def state_relations_axioms subrelI)

lemma "\<lpred>id_rel\<rpred> = id_bar fempty"
  by (smt (verit, ccfv_SIG) Collect_cong UNIV_I ex_fin_conv id_bar_def id_rel_def prod.collapse relation_def split_def)

lemma "\<lpred>id_rel_bar xs\<rpred> = id_bar xs"
  by (smt (verit, del_insts) Collect_cong UNIV_I case_prod_unfold fst_conv id_bar_def id_rel_bar_def relation_def snd_conv)
end

locale ctxt = strong_spec + seq 

text \<open>Below are some results around program refinement\<close>
context strong_spec
begin
lemma 
  assumes "\<And>x. p1 x \<Longrightarrow> p2 x"
  shows "\<lbrace>\<lrel>p1\<rrel>\<rbrace> \<ge> \<lbrace>\<lrel>p2\<rrel>\<rbrace>"
  by (metis Collect_mono assert_iso assms predset_def)

lemma 
  assumes "\<And>s s'. (p s \<and> q2 (s, s')) \<Longrightarrow> q1 (s, s')"
  shows "\<lbrace>\<lrel>p\<rrel>\<rbrace>;\<lparr>\<lpred>q1\<rpred>\<rparr> \<ge> \<lbrace>\<lrel>p\<rrel>\<rbrace>;\<lparr>\<lpred>q2\<rpred>\<rparr>"
proof - 
  have "\<And>s s'. (p s \<and> q2 (s, s')) \<Longrightarrow> (p \<triangleleft> q1)" by sledgehammer



end
end