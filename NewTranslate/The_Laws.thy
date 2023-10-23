theory The_Laws
  imports 
    "./Predicates"
    "../Programming/IntroPar_Big"
    "../Programming/State_Relations"
    "../Programming/Assignments"
begin

text \<open>Below are some results around program refinement\<close>

locale laws = strong_spec + intro_par_big + state_relations + expressions + assignments
begin

lemma relat_ge: "\<lceil>\<lpred>q1\<rpred> \<sqinter> \<lpred>q2\<rpred>\<rceil> \<ge> \<lparr>\<lpred>q1 |\<and>| q2\<rpred>\<rparr>"
 by (metis (mono_tags, opaque_lifting) Int_subset_iff conj.sync_mono conj_chaos lambda_and_def pspec_strengthen rel_eq spec_def term_nonaborting)

lemma relat_le "\<lparr>\<lpred>q1 |\<and>| q2\<rpred>\<rparr> \<ge> \<lceil>\<lpred>q1\<rpred> \<sqinter> \<lpred>q2\<rpred>\<rceil>"
proof -
  have "\<lparr>\<lpred>q1 |\<and>| q2\<rpred>\<rparr> = \<lparr>\<lpred>(\<lambda>s. q1 s \<and> q2 s)\<rpred>\<rparr>"
    by (simp add: lambda_and_def) 
  have "... = \<lparr>{s. q1 s \<and> q2 s}\<rparr>"
    by (simp add: relation_def)
  have "... = \<lparr>{s. q1 s} \<inter> {s. q2 s}\<rparr>"
    by (simp add: Collect_conj_eq)
  have "... = \<lparr>\<lpred>q1\<rpred> \<inter> \<lpred>q2\<rpred>\<rparr>"
    by (simp add: relation_def)
  have "... = \<lparr>\<lpred>q1\<rpred> \<sqinter> \<lpred>q2\<rpred>\<rparr>"
    by auto
  have "... \<ge> \<lceil>\<lpred>q1\<rpred> \<sqinter> \<lpred>q2\<rpred>\<rceil> \<iinter> term" by sledgehammer
qed

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
  shows "\<lparr>\<lpred>q1 \<Zcomp> q2\<rpred>\<rparr> \<ge> \<lparr>\<lpred>q1\<rpred>\<triangleright>\<lrel>p1\<rrel>\<rparr>;\<lbrace>\<lrel>p1\<rrel>\<rbrace>;\<lparr>\<lpred>q2\<rpred>\<rparr>"
  by (simp add: relseqeq spec_seq_introduce)

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
  shows "(guar \<lpred>g1\<rpred>) \<iinter> (guar \<lpred>g2\<rpred>) \<ge> guar \<lpred>(g1 |\<and>| g2)\<rpred>"
  by (metis conj_refine lambda_and_def strengthen_guar)

lemma distrib_guar_seq:
  shows "(guar g) \<iinter> (c;d) \<ge> ((guar g) \<iinter> c) ; ((guar g) \<iinter> d)"
  using guar_distrib_seq by blast

lemma distrib_guar_par:
  shows "(guar g) \<iinter> (c\<parallel>d) \<ge> ((guar g) \<iinter> c) \<parallel> ((guar g) \<iinter> d)"
  using guar_distrib_par by blast

lemma distrib_guar_multipar:
  assumes "finite A"
  assumes "A \<noteq> {}"
  shows "((guar g) \<iinter> (\<parallel>\<parallel>\<in>A. (\<lambda>x. x))) \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. (guar g) \<iinter> x))"
  by (smt (verit, del_insts) assms(1) assms(2) conj_setpar_distrib guar_distrib_seq guar_par_idem guar_seq_idem local.conj.idem setpar.cong)

lemma restrict_frame:
  assumes "Y |\<subseteq>| X"
  shows "X:\<^sub>sc \<ge> Y:\<^sub>sc"
  using assms conj.sync_mono_left guar_strengthen id_bar_narrow var_frame_set_def by presburger

lemma introduce_para:
  shows "(rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>(q1 |\<and>| q2)\<rpred>\<rparr> \<ge> 
         ((rely \<lpred>(r |\<or>| r1)\<rpred>) \<iinter> (guar \<lpred>r2\<rpred>) \<iinter> \<lparr>\<lpred>q1\<rpred>\<rparr>)
         \<parallel> ((rely \<lpred>(r |\<or>| r2)\<rpred>) \<iinter> (guar \<lpred>r1\<rpred>) \<iinter> \<lparr>\<lpred>q2\<rpred>\<rparr>)"
proof - 
  have "(rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>(q1 |\<and>| q2)\<rpred>\<rparr> \<ge> (rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>(q1 |\<and>| q2)\<rpred>\<rparr> \<iinter> term" 
    using conj_conjoin_non_aborting term_nonaborting by force
  also have "(rely \<lpred>r\<rpred>) \<iinter> \<lceil>\<lpred>q1\<rpred> \<sqinter> \<lpred>q2\<rpred>\<rceil> \<iinter> term \<ge> (rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>(q1 |\<and>| q2)\<rpred>\<rparr> \<iinter> term" (is "_ \<ge> ?rhs")
    using conj.sync_mono_right local.conj_commute relat_eq by presburger
  also have  \<ge> ((guar \<lpred>r |\<or>| r2\<rpred>) \<iinter> (rely \<lpred>r |\<or>| r1\<rpred>) \<iinter> \<lparr>\<lpred>q1\<rpred>\<rparr> \<parallel> (guar \<lpred>r |\<or>| r1\<rpred>) \<iinter> (rely \<lpred>r |\<or>| r2\<rpred>) \<iinter> \<lparr>\<lpred>q2\<rpred>\<rparr>) \<iinter> term" by sledgehammer
qed

lemma introduce_multi_para:
  assumes "finite A"
  assumes "A \<noteq> {}"
  shows "(rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>|\<And>|A\<rpred>\<rparr> \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>q. (guar \<lpred>r1\<rpred>) \<iinter> (rely \<lpred>(r |\<or>| r1)\<rpred>) \<iinter> \<lparr>\<lpred>q\<rpred>\<rparr>))" 
  sorry

lemma trading:
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lparr>\<lpred>q\<rpred>\<rparr> = (rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lparr>\<lpred>(r |\<or>| g)\<rpred>\<^sup>* \<inter> \<lpred>q\<rpred>\<rparr>"
  sorry

definition pstable :: "('state \<Rightarrow> bool) \<Rightarrow> (('state*'state) \<Rightarrow> bool) \<Rightarrow> bool"
  where "pstable p r \<equiv> \<forall> s. r s \<longrightarrow> (p (fst s) \<longrightarrow> p (snd s))"

definition qtolerates :: "('state \<Rightarrow> bool) \<Rightarrow> (('state*'state) \<Rightarrow> bool) \<Rightarrow> (('state*'state) \<Rightarrow> bool) \<Rightarrow> bool" 
  where "qtolerates p q r
     \<equiv> (pstable p r)
     \<and> (\<forall>s. (p (fst s) \<and> (r \<Zcomp> q) s) \<longrightarrow> q s)
     \<and> (\<forall>s. (p (fst s) \<and> (q \<Zcomp> r) s) \<longrightarrow> q s)"

definition const_exp :: "('state, 'v) expr \<Rightarrow> (('state*'state) \<Rightarrow> bool) \<Rightarrow> bool"
  where "const_exp e r \<equiv> \<forall> (s, s')\<in>\<lpred>r\<rpred>. eval e s = eval e s'"

fun sin_ref_exp :: "('state,'v) expr \<Rightarrow> (('state*'state) \<Rightarrow> bool) \<Rightarrow> bool" where
  "sin_ref_exp (Constant k) r = True" | 
  "sin_ref_exp (Variable accessor) r = True" | 
  "sin_ref_exp (UnaryOp oper e1) r = (sin_ref_exp e1 r)" |
  "sin_ref_exp (BinaryOp oper e1 e2) r = 
      ((sin_ref_exp e1 r) \<and> (sin_ref_exp e2 r) \<and> 
      ((const_exp e1 r) \<or> (const_exp e2 r)))"

definition atomic_exp :: "('b \<Rightarrow> bool) \<Rightarrow> ('b*'b \<Rightarrow> bool) \<Rightarrow> 'a" ("\<langle>_,_\<rangle>" [30, 30])
  where "atomic_exp p q \<equiv> opt (\<lrel>p\<rrel> \<triangleleft> \<lpred>q\<rpred>)"

lemma intro_atomic:
  assumes "pstable p r \<and> refl \<lpred>g\<rpred> \<and> qtolerates p q r"
  shows "(guar \<lpred>g\<rpred>) \<iinter> (rely \<lpred>r\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;\<lparr>\<lpred>q\<rpred>\<rparr> \<ge> (rely \<lpred>r\<rpred>) \<iinter> \<langle>p, (g |\<and>| q)\<rangle>"
  sorry

lemma local_ass:
  assumes "sin_ref_exp e r"
  assumes "const_exp e r"
  assumes "pstable p r"
  assumes "qtolerates p q r"
  assumes "refl \<lpred>g\<rpred>"
  assumes "\<forall>s. (p (fst s) \<and> id\<^sub>x s) \<longrightarrow> (g |\<and>| q) (fst s, set_var x (eval e (fst s)) (snd s))"
  shows "(rely \<lpred>r\<rpred> ) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;x:\<^sub>f\<lparr>\<lpred>q\<rpred>\<rparr> \<ge> x ::= e"
  sorry

lemma post_ass:
  assumes "sin_ref_exp e r"
  assumes "const esp e r"
  assumes "pstable p0 r"
  assumes "pstable p1 r"
  assumes "qtolerates p q r"
  assumes "refl \<lpred>g\<rpred>"
  assumes "\<forall>s. (p1 (fst s) \<and> id\<^sub>x s) \<longrightarrow> g (fst s, set_var x (eval e (fst s)) (snd s))"
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p0\<rrel>\<rbrace>;x:\<^sub>f\<lparr>\<lpred>q\<rpred>\<rparr> \<ge> ((rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p0\<rrel>\<rbrace>;\<lparr>\<lpred>(\<lambda>(s, s').q (s, set_var x (eval e s') s') \<and> p1 s')\<rpred>\<rparr>);(x ::= e)"
  sorry

lemma rely_ass:
  fixes gte :: "'d \<Rightarrow> 'd \<Rightarrow> bool" (infix "\<succeq>" 50)
  assumes "pstable p r"
  assumes "const_exp (Constant x) r"
  assumes "sin_ref_exp e r"
  assumes "refl \<lpred>case_prod gte\<rpred> \<and> trans \<lpred>case_prod gte\<rpred>"
  assumes "\<forall>s. ((id\<^sub>x s \<or> r s) \<longrightarrow> ((eval e (fst s)) \<succeq> (eval e (snd s)))) \<and> (((p (fst s) \<and> id\<^sub>x s)) \<longrightarrow> g (fst s, set_var x (eval e (fst s)) (snd s)))"
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;x:\<^sub>f\<lparr>\<lpred>(\<lambda>(\<sigma>, \<sigma>'). eval e \<sigma> \<succeq> get_var x \<sigma>' \<and> get_var x \<sigma>' \<succeq> eval e \<sigma>')\<rpred>\<rparr> \<ge> (x ::= e) "
  sorry

lemma intro_var:
  assumes "pstable p r"
  assumes "qtolerates p q r"
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>(\<lambda>(s, s'). get_var x s' = get_var x s \<and> (\<exists>s. g s))\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;Y:\<^sub>s\<lparr>\<lpred>(\<lambda>s. \<exists>s. q s)\<rpred>\<rparr> \<ge> 
         (rely \<lpred>(\<lambda>(s, s'). get_var x s' = get_var x s \<and> (\<exists>s. r s))\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>(\<lambda>s. \<exists>s. p s)\<rrel>\<rbrace>;({|x|} |\<union>| Y):\<^sub>s\<lparr>\<lpred>q\<rpred>\<rparr>" 
  sorry (*this one is written wrong with the \<exists>*)


end


end