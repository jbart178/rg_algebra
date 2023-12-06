theory The_Laws
  imports 
    "./Predicates"
    "../Programming/Programming_Constructs"
    "../Programming/AtomicSpecification"
begin

syntax 
"_assign" :: "idt \<Rightarrow> 'b \<Rightarrow> 'a" ("(\<Zprime>_ |:=| _)" [70, 65] 61)

translations
"\<Zprime>x |:=| a" \<rightharpoonup> "\<guillemotleft>\<Zprime>(_update_name x (\<lambda>_. a))\<guillemotright>"


text \<open>Below are some results around program refinement\<close>

locale laws = programming_constructs_simple + atomic_specification
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

lemma conj_to_inter:
  shows "\<lpred>(q1 |\<and>| q2)\<rpred> = \<lpred>q1\<rpred> \<sqinter> \<lpred>q2\<rpred>"
  by (simp add: Int_def lambda_and_def relation_def)

lemma conj_to_inter_round:
  shows "\<lpred>(q1 |\<and>| q2)\<rpred> = \<lpred>q1\<rpred> \<inter> \<lpred>q2\<rpred>"
  by (meson conj_to_inter)

lemma or_to_union:
  shows "\<lpred>(q1 |\<or>| q2)\<rpred> = \<lpred>q1\<rpred> \<squnion> \<lpred>q2\<rpred>"
proof -
  have 1: "\<lpred>(q1 |\<or>| q2)\<rpred> = {x. q1 x \<or> q2 x}"
    by (simp add: lambda_or_def relation_def)
  also have "\<lpred>q1\<rpred> \<squnion> \<lpred>q2\<rpred> = {x. q1 x} \<squnion> {x. q2 x}"
    by (simp add: relation_def)
  hence "... = {x. q1 x \<or> q2 x}"
    by blast
  thus "?thesis" using 1 by (simp add: relation_def)
qed

lemma conj_to_inter_big:
  shows "\<lpred>|\<And>|A\<rpred> = (\<Sqinter>q\<in>A. \<lpred>q\<rpred>)"
proof -
  have "\<lpred>|\<And>|A\<rpred> \<subseteq> (\<Sqinter>q\<in>A. \<lpred>q\<rpred>)"
    by (metis (mono_tags, lifting) INT_greatest lambda_and_big_def rel_eq)
  also have "(\<Sqinter>q\<in>A. \<lpred>q\<rpred>) \<subseteq> \<lpred>|\<And>|A\<rpred>"
    by (smt (verit) INT_iff lambda_and_big_def mem_Collect_eq relation_def subsetI)
  thus "?thesis" using calculation by force
qed

lemma introduce_para:
  shows "(rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>(q1 |\<and>| q2)\<rpred>\<rparr> \<ge> 
         ((rely \<lpred>(r |\<or>| r1)\<rpred>) \<iinter> (guar \<lpred>r2\<rpred>) \<iinter> \<lparr>\<lpred>q1\<rpred>\<rparr>)
         \<parallel> ((rely \<lpred>(r |\<or>| r2)\<rpred>) \<iinter> (guar \<lpred>r1\<rpred>) \<iinter> \<lparr>\<lpred>q2\<rpred>\<rparr>)"
proof - 
  have 1: "(rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>(q1 |\<and>| q2)\<rpred>\<rparr> = (rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>q1\<rpred> \<sqinter> \<lpred>q2\<rpred>\<rparr>"
    by (simp add: conj_to_inter)
  hence 2: "... \<ge> ((rely (\<lpred>r\<rpred> \<squnion> \<lpred>r1\<rpred>)) \<iinter> (guar (\<lpred>r\<rpred> \<squnion> \<lpred>r2\<rpred>)) \<iinter> \<lparr>\<lpred>q1\<rpred>\<rparr>)
         \<parallel> ((rely (\<lpred>r\<rpred> \<squnion> \<lpred>r2\<rpred>)) \<iinter> (guar (\<lpred>r\<rpred> \<squnion> \<lpred>r1\<rpred>)) \<iinter> \<lparr>\<lpred>q2\<rpred>\<rparr>)" (is "_\<ge>?rhs")
    using local.conj_commute spec_introduce_par by presburger
  hence 3: "?rhs = ((rely \<lpred>(r |\<or>| r1)\<rpred>) \<iinter> (guar \<lpred>r |\<or>| r2\<rpred>) \<iinter> \<lparr>\<lpred>q1\<rpred>\<rparr>) \<parallel> ((rely \<lpred>(r |\<or>| r2)\<rpred>) \<iinter> (guar \<lpred>r |\<or>| r1\<rpred>) \<iinter> \<lparr>\<lpred>q2\<rpred>\<rparr>)"
    by (simp add: or_to_union)
  hence 4: "... \<ge> ((rely \<lpred>(r |\<or>| r1)\<rpred>) \<iinter> (guar \<lpred>r2\<rpred>) \<iinter> \<lparr>\<lpred>q1\<rpred>\<rparr>) \<parallel> ((rely \<lpred>(r |\<or>| r2)\<rpred>) \<iinter> (guar \<lpred>r1\<rpred>) \<iinter> \<lparr>\<lpred>q2\<rpred>\<rparr>)"
  by (smt (verit, ccfv_SIG) Int_subset_iff Un_Int_eq(2) or_to_union guar_rely_refine_guar_pgm monotonicity(2) monotonicity(3) order.refl)
  thus "?thesis"
    using "1" "2" "3" by auto
qed

lemma introduce_multi_para:
  assumes "finite A"
  assumes "A \<noteq> {}"
  shows "(rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>|\<And>|A\<rpred>\<rparr> \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>q. (guar \<lpred>r\<rpred>) \<iinter> (rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>q\<rpred>\<rparr>))" 
proof - 
  have "(rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<lpred>|\<And>|A\<rpred>\<rparr> = (rely \<lpred>r\<rpred>) \<iinter> \<lparr>\<Sqinter>q\<in>A. \<lpred>q\<rpred>\<rparr>"
    by (simp add: conj_to_inter_big)
  thus "?thesis"
    by (metis assms(1) assms(2) spec_introduce_par_big)
qed

lemma trading:
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lparr>\<lpred>q\<rpred>\<rparr> = (rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lparr>\<lpred>(r |\<or>| g)\<rpred>\<^sup>* \<inter> \<lpred>q\<rpred>\<rparr>"
  by (metis or_to_union spec_trading)

lemma intro_atomic:
  assumes stable: "stable \<lrel>p\<rrel> \<lpred>r\<rpred>"
  assumes refl: "refl \<lpred>g\<rpred>"
  assumes tolerates: "tolerates_interference \<lrel>p\<rrel> \<lpred>q\<rpred> \<lpred>r\<rpred>"
  shows "(guar \<lpred>g\<rpred>) \<iinter> (rely \<lpred>r\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;\<lparr>\<lpred>q\<rpred>\<rparr> \<ge> (rely \<lpred>r\<rpred>) \<iinter> \<langle>\<lrel>p\<rrel>,\<lpred>g |\<and>| q\<rpred>\<rangle>"
  by (metis atomic_spec_introduce conj_to_inter_round local.conj_commute local.refl tolerates)

text \<open>After here we will benefit from the RG_Hoare syntax\<close>

(*
fun change_com :: "'a com \<Rightarrow> 'a" where
  "change_com (Basic c) = c s" |
  "change_com (Seq c d) = (change_com c) ; (change_com d)" |
  "change_com (Cond b c d) = if_statement b (change_com c) (change_com d)" |
  "change_com (While b c) = while_statement b (change_com c)" |
  "change_com (Await b c) = idle"
*)


lemma assign_hoare: "(y ::= e) \<equiv> \<Squnion>k. (\<lbrakk>e\<rbrakk>k ; opt(\<lpred>id\<^sub>x\<rpred> \<triangleright> Collect (\<Zprime>x |:=| (eval e s))) ; idle)"
  by sledgehammer

lemma local_ass:
  assumes single_reference_e: "single_reference e \<lpred>r\<rpred>"
  assumes estable_e: "estable e \<lpred>r\<rpred>"
  assumes stable: "stable \<lrel>p\<rrel> \<lpred>r\<rpred>"
  assumes tolerates_q: "tolerates_interference \<lrel>p\<rrel> \<lpred>q\<rpred> \<lpred>r\<rpred>"
  assumes refl_g: "refl \<lpred>g\<rpred>"
  assumes "\<forall>s. (p (fst s) \<and> id\<^sub>x s) \<longrightarrow> (g |\<and>| q |\<and>| \<guillemotleft>\<ordfeminine>x = eval e\<guillemotright>) s"
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;\<lparr>\<lpred>q\<rpred>\<rparr> \<ge> \<acute>x := e"
  by sledgehammer

lemma post_ass:
  assumes "single_reference e \<lpred>r\<rpred>"
  assumes "estable e \<lpred>r\<rpred>"
  assumes "stable \<lrel>p0\<rrel> \<lpred>r\<rpred>"
  assumes "stable \<lrel>p1\<rrel> \<lpred>r\<rpred>"
  assumes "tolerates_interference \<lrel>p\<rrel> \<lpred>q\<rpred> \<lpred>r\<rpred>"
  assumes stable: "stable \<lrel>p\<rrel> \<lpred>r\<rpred>"
  assumes tolerates_q: "tolerates_interference \<lrel>p\<rrel> \<lpred>q\<rpred> \<lpred>r\<rpred>"
  assumes refl_g: "refl \<lpred>g\<rpred>"
  assumes "\<forall>s. (p (fst s) \<and> id\<^sub>x s) \<longrightarrow> (g |\<and>| q) (fst s, set_var x (eval e (fst s)) (snd s))"
  shows "(rely \<lpred>r\<rpred> ) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;x:\<^sub>f\<lparr>\<lpred>q\<rpred>\<rparr> \<ge> x ::= e"
  by sledgehammer

lemma post_ass:"refl \<lpred>g\<rpred>"
  assumes "\<forall>s. (p1 (fst s) \<and> id\<^sub>x s) \<longrightarrow> g (fst s, set_var x (eval e (fst s)) (snd s))"
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p0\<rrel>\<rbrace>;x:\<^sub>f\<lparr>\<lpred>q\<rpred>\<rparr> \<ge> ((rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p0\<rrel>\<rbrace>;\<lparr>\<lpred>(\<lambda>(s, s').q (s, set_var x (eval e s') s') \<and> p1 s')\<rpred>\<rparr>);(x ::= e)"
  by sledgehammer

lemma rely_ass:
  fixes gte :: "'d \<Rightarrow> 'd \<Rightarrow> bool" (infix "\<succeq>" 50)
  assumes "stable \<lrel>p\<rrel> \<lpred>r\<rpred>"
  assumes "estable (Constant x) \<lpred>r\<rpred>"
  assumes "single_reference e \<lpred>r\<rpred>"
  assumes "refl \<lpred>case_prod gte\<rpred> \<and> trans \<lpred>case_prod gte\<rpred>"
  assumes "\<forall>s. ((id\<^sub>x s \<or> r s) \<longrightarrow> ((eval e (fst s)) \<succeq> (eval e (snd s)))) \<and> (((p (fst s) \<and> id\<^sub>x s)) \<longrightarrow> g (fst s, set_var x (eval e (fst s)) (snd s)))"
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;x:\<^sub>f\<lparr>\<lpred>(\<lambda>(\<sigma>, \<sigma>'). eval e \<sigma> \<succeq> get_var x \<sigma>' \<and> get_var x \<sigma>' \<succeq> eval e \<sigma>')\<rpred>\<rparr> \<ge> (x ::= e) "
  by sledgehammer

lemma intro_var:
  assumes "stable \<lrel>p\<rrel> \<lpred>r\<rpred>"
  assumes "tolerates_interference \<lrel>p\<rrel> \<lpred>q\<rpred> \<lpred>r\<rpred>"
  shows "(rely \<lpred>r\<rpred>) \<iinter> (guar \<lpred>(\<lambda>(s, s'). get_var x s' = get_var x s \<and> (\<exists>s. g s))\<rpred>) \<iinter> \<lbrace>\<lrel>p\<rrel>\<rbrace>;Y:\<^sub>s\<lparr>\<lpred>(\<lambda>s. \<exists>s. q s)\<rpred>\<rparr> \<ge> 
         (rely \<lpred>(\<lambda>(s, s'). get_var x s' = get_var x s \<and> (\<exists>s. r s))\<rpred>) \<iinter> (guar \<lpred>g\<rpred>) \<iinter> \<lbrace>\<lrel>(\<lambda>s. \<exists>s. p s)\<rrel>\<rbrace>;({|x|} |\<union>| Y):\<^sub>s\<lparr>\<lpred>q\<rpred>\<rparr>" 
  sorry (*this one is written wrong with the \<exists>*)


end


end