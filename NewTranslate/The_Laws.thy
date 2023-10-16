theory The_Laws
  imports 
    "./Predicates"
    "../Programming/IntroPar_Big"

begin

text \<open>Below are some results around program refinement\<close>

locale laws = strong_spec + intro_par_big
begin

lemma monotonicity:
  assumes "c0 \<ge> c1 \<and> d0 \<ge> d1"
  shows "c0 ; d0 \<ge> c1 ; d1" 
    and "c0 \<parallel> d0 \<ge> c1 \<parallel> d1"
    and "c0 \<iinter> d0 \<ge> c1 \<iinter> d1"
  apply (simp add: assms seq_mono)
  apply (simp add: assms par.sync_mono)
  apply (simp add: assms conj.sync_mono)
  done

lemma weaken_pre:
  assumes "\<forall>x. p1 x \<longrightarrow> p2 x"
  shows "\<lbrace>\<lrel>p1\<rrel>\<rbrace> \<ge> \<lbrace>\<lrel>p2\<rrel>\<rbrace>"
  by (metis Collect_mono assert_iso assms predset_def)

lemma remove_pre:
  shows "\<lbrace>p\<rbrace>;c \<ge> c"
  by (simp add: assert_remove_left)

lemma strengthen_post_pre:
  assumes "\<forall>s s'. (p s \<and> q2 (s, s')) \<longrightarrow> q1 (s, s')"
  shows "\<lbrace>\<lrel>p\<rrel>\<rbrace>;\<lparr>\<lpred>q1\<rpred>\<rparr> \<ge> \<lbrace>\<lrel>p\<rrel>\<rbrace>;\<lparr>\<lpred>q2\<rpred>\<rparr>"
  by (metis assms dom_restrict prod.collapse spec_strengthen_under_pre)

lemma sequential:
  shows "\<lparr>\<lpred>q1\<rpred> O \<lpred>q2\<rpred>\<rparr> \<ge> \<lparr>\<lpred>q1\<rpred>\<triangleright>\<lrel>p1\<rrel>\<rparr>;\<lbrace>\<lrel>p1\<rrel>\<rbrace>;\<lparr>\<lpred>q2\<rpred>\<rparr>"
  using spec_seq_introduce by auto

lemma weaken_rely:
  assumes "\<forall> s. r1 s \<longrightarrow> r2 s"
  shows "rely \<lpred>r1\<rpred> \<ge> rely \<lpred>r2\<rpred>"
  by (metis assms rel_eq rely_weaken)

lemma remove_rely:
  shows "(rely r) \<iinter> c \<ge> c"
  using rely_remove by auto

lemma refine_within_rely:
  assumes "(rely r) \<iinter> c2 \<ge> (rely r) \<iinter> d"
  shows "(rely r) \<iinter> c1;c2;c3 \<ge> (rely r) \<iinter> c1;d;c3"
  using assms rely_refine_within by blast

lemma strengthen_guar:
  assumes "\<forall> s. g2 s \<longrightarrow> g1 s"
  shows "guar \<lpred>g1\<rpred> \<ge> guar \<lpred>g2\<rpred>"
  using assms guar_strengthen rel_eq by blast

lemma introduce_guar:
  shows "c \<ge> (guar g) \<iinter> c"
  using guar_introduce by force

lemma merge_guars:
  shows "(guar \<lpred>g1\<rpred>) \<iinter> (guar \<lpred>g2\<rpred>) \<ge> guar \<lpred>(\<lambda>s. g1 s \<and> g2 s)\<rpred>"
  using conj_refine strengthen_guar by presburger

lemma distrib_guar_seq:
  shows "(guar g) \<iinter> (c;d) \<ge> ((guar g) \<iinter> c) ; ((guar g) \<iinter> d)"
  using guar_distrib_seq by blast

lemma distrib_guar_par:
  shows "(guar g) \<iinter> (c\<parallel>d) \<ge> ((guar g) \<iinter> c) \<parallel> ((guar g) \<iinter> d)"
  using guar_distrib_par by blast

(*
lemma distrib_guar_multipar:
  shows "(guar g) \<iinter> (\<parallel>i ci) \<ge> \<parallel>i ((guar g) \<iinter> ci)"
  by sledgehammer
*)

lemma restrict_frame:
  assumes "X \<subseteq> Y"
  shows "X:c \<ge> Y:c"

end


end