theory Predicates
  imports
    "Main"
    "../General/Relations"
    "../Programming/State_Relations"
begin

text \<open>We use (\<lpred>p\<rpred>) to give a relation where (\<sigma>,\<sigma>') satisfy predicate p\<close>


definition relation :: "(('a*'a) \<Rightarrow> bool) \<Rightarrow> 'a rel" ("\<lpred>_\<rpred>" [30])
  where "relation r \<equiv> {(s, s') \<in> UNIV. r (s, s')} "

definition predset :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" ("\<lrel>_\<rrel>" [30])
  where "predset p = Collect(p)"

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




lemma rel_eq: "(\<lpred>q1\<rpred> \<subseteq> \<lpred>q2\<rpred>) = (\<forall> s. q1 s \<longrightarrow> q2 s)"
proof -
  have "\<lpred>q1\<rpred> \<subseteq> \<lpred>q2\<rpred> \<Longrightarrow> (\<forall> x. q1 x \<longrightarrow> q2 x)" by (metis (mono_tags, lifting) Collect_mono_iff UNIV_I prod.collapse relation_def split_def)
  also have "(\<forall> x. q1 x \<longrightarrow> q2 x) \<Longrightarrow> \<lpred>q1\<rpred> \<subseteq> \<lpred>q2\<rpred>" using relation_def by auto
  thus ?thesis using calculation by blast
  qed

lemma pred_eq: "(\<lrel>p1\<rrel> \<subseteq> \<lrel>p2\<rrel>) = (\<forall>s. p1 s \<longrightarrow> p2 s)"
  by (simp add: Collect_mono_iff predset_def)

lemma dom_restrict: "(\<lrel>p\<rrel> \<triangleleft> \<lpred>q2\<rpred> \<subseteq> \<lpred>q1\<rpred>) = (\<forall>s. p (fst s) \<and> q2 s \<longrightarrow> q1 s)"
  by (simp add: Collect_mono_iff Int_def predset_def relation_def restrict_domain_def)

lemma range_restrict: "(\<lpred>q2\<rpred> \<triangleright> \<lrel>p\<rrel> \<subseteq> \<lpred>q1\<rpred>) = (\<forall>s. p (snd s) \<and> q2 s \<longrightarrow> q1 s)"
  by (smt (verit) Int_iff UNIV_def mem_Collect_eq predset_def prod.collapse relation_def restrict_range_def split_def subset_iff)


lemma "(Range (\<lrel>p\<rrel> \<triangleleft> \<lpred>r\<rpred>)) \<subseteq> (\<lpred>r\<rpred> `` \<lrel>p\<rrel>)"
  using restrict_domain_def by fastforce
end