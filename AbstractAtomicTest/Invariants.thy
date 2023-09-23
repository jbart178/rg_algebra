section \<open>Invariants\<close>

theory Invariants
  imports
  "AtomicSpecification"
  "Local"
begin                                   
                       
locale invariants = locals + atomic_specification
begin                  

(*
For completeness
lemma "restrict_range UNIV p = range_restriction p" (= {(\<sigma>, \<sigma>'). p \<in> \<sigma>'} as in the paper)
proof -
  have "restrict_range UNIV p = UNIV \<inter> range_restriction p" unfolding restrict_range_def by simp
  also have "... = range_restriction p"
    by simp
  finally show ?thesis .
qed
*)

definition inv :: "'b set \<Rightarrow> 'a" where
  "inv p \<equiv> \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>"

definition gen_inv :: "'b set \<Rightarrow> 'a" ("\<box>")
  where "\<box>p = \<tau>(p) ; inv p" 

lemma gen_inv_def_2: "\<box>p = \<tau>(p) ; guar\<^sub>\<alpha> (UNIV \<triangleright> p)"
  by (metis gen_inv_def inv_def guar\<^sub>\<alpha>_def)

lemma inv_preserve_helper: "(p \<triangleleft> UNIV) \<inter> (UNIV \<triangleright> p) \<subseteq> UNIV \<triangleright> p"
  by simp

lemma inv_preserve_test: "\<box>p = \<box>p ; \<tau> p"
  by (simp add: inv_preserve_helper gen_inv_def_2 evolve_preserve_test_guar_atomic)

lemma inv_preserve_conj: "\<box>p \<iinter> c = (\<box>p \<iinter> c) ; \<tau> p"
  by (metis conj.test_sync_post inv_preserve_test local.conj_commute)

lemma inv_preserve_conj_fiter: "\<tau> p ; (\<box>p \<iinter> c)\<^sup>\<star> = \<tau> p ; (\<box>p \<iinter> c)\<^sup>\<star> ; \<tau> p"
  by (metis inv_preserve_conj par.fiter_leapfrog seq_assoc test_seq_idem)

lemma inv_preserve_conj_iter: "\<tau> p ; (\<box>p \<iinter> c)\<^sup>\<omega> = \<tau> p ; (\<box>p \<iinter> c)\<^sup>\<omega> ; \<tau> p"
  by (metis inv_preserve_conj par.iter_leapfrog seq_assoc test_seq_idem)

lemma inv_preserve_conj_seq: "\<tau> p ; (\<box>p \<iinter> (c\<^sub>1 ; c\<^sub>2)) = \<tau> p ; (\<box>p \<iinter> c\<^sub>1) ; \<tau> p ; (\<box>p \<iinter> c\<^sub>2)"
proof -
  have "\<tau> p ; (\<box>p \<iinter> (c\<^sub>1 ; c\<^sub>2)) = \<tau> p ; (\<tau>(p) ; guar\<^sub>\<alpha>(UNIV \<triangleright> p) \<iinter> (c\<^sub>1 ; c\<^sub>2))"
    by (metis gen_inv_def_2)
  also have "... = \<tau> p ; \<tau>(p) ; guar\<^sub>\<alpha>(UNIV \<triangleright> p) \<iinter> \<tau> p ; (c\<^sub>1 ; c\<^sub>2)"
    by (simp add: seq_assoc test_conj_distrib)
  also have "... = \<tau>(p) ; (guar\<^sub>\<alpha>(UNIV \<triangleright> p) \<iinter> (c\<^sub>1 ; c\<^sub>2))"
    by (metis test_conj_distrib test_seq_idem)
  also have "... = \<tau> p ; (guar\<^sub>\<alpha>(UNIV \<triangleright> p) \<iinter> c\<^sub>1) ; \<tau> p ; (guar\<^sub>\<alpha>(UNIV \<triangleright> p) \<iinter> c\<^sub>2)"
    by (simp add: evolve_preserve_test_guar_atomic_conj_seq)
  finally show ?thesis
    by (metis seq_assoc test_conj_distrib test_seq_idem gen_inv_def_2)
qed

lemma evolve_equivalent_under_inv:
  assumes "(p \<triangleleft> UNIV) \<inter> r\<^sub>1 = (p \<triangleleft> UNIV) \<inter> r\<^sub>2"
  assumes "(p \<triangleleft> UNIV) \<inter> r\<^sub>1 \<subseteq> UNIV \<triangleright> p"
  shows "\<tau> p ; guar\<^sub>\<alpha> r\<^sub>1 = \<tau> p ; guar\<^sub>\<alpha> r\<^sub>2"
proof -
  have a1: "\<tau> p ; \<alpha> r\<^sub>1 = \<tau> p ; \<alpha> r\<^sub>2"
    by (simp add: assms(1) atomic_pull_test)
  have a2: "\<tau> p ; \<alpha> r\<^sub>1 ; \<tau> p = \<tau> p ; \<alpha> r\<^sub>1"
    by (simp add: assms(2) step_preserve_prop)
  show ?thesis
    by (metis a1 a2 par.equivalent_under_inv guar\<^sub>\<alpha>_def)
qed

lemma guarded_evolve: "\<tau> p ; guar\<^sub>\<alpha>(UNIV \<triangleright> p) = \<tau> p ; guar\<^sub>\<alpha>((UNIV \<triangleright> p) \<union> -(p \<triangleleft> UNIV)) \<and> \<tau> p ; guar\<^sub>\<alpha>(UNIV \<triangleright> p) = \<tau> p ; guar\<^sub>\<alpha>((p \<triangleleft> UNIV) \<inter> (UNIV \<triangleright> p))"
proof -
  have "(p \<triangleleft> UNIV) \<inter> (UNIV \<triangleright> p) = (p \<triangleleft> UNIV) \<inter> ((UNIV \<triangleright> p) \<union> -(p \<triangleleft> UNIV))"
    by blast
  then show ?thesis
    using evolve_equivalent_under_inv by blast
qed

lemma inv_strengthen:
  assumes "p\<^sub>1 \<supseteq> p\<^sub>2"
  shows "inv p\<^sub>1 \<ge> inv p\<^sub>2"
proof -
  have "UNIV \<triangleright> p\<^sub>1 \<ge> UNIV \<triangleright> p\<^sub>2"
    by (simp add: assms range_restrict_p_mono)
  then have "\<alpha>(UNIV \<triangleright> p\<^sub>1) \<ge> \<alpha>(UNIV \<triangleright> p\<^sub>2)"
    using general_atomic.hom_mono by auto
  then have "\<alpha>(UNIV \<triangleright> p\<^sub>1)\<^sup>\<omega> \<ge> \<alpha>(UNIV \<triangleright> p\<^sub>2)\<^sup>\<omega>"
    using iter_mono by auto
  then show ?thesis using inv_def by simp
qed

lemma gen_inv_strengthen:
  assumes "p\<^sub>1 \<supseteq> p\<^sub>2"
  shows "\<box>p\<^sub>1 \<ge> \<box>p\<^sub>2"
proof -
  show ?thesis
    by (simp add: assms gen_inv_def inv_strengthen seq_mono test.hom_mono)
qed

lemma inv_introduce: "c \<ge> inv p \<iinter> c"
proof -
  have inv_chaos: "inv UNIV = chaos"
    by (simp add: restrict_range_def inv_def Atomic_def2 general_atomic_def env.Hom_def pgm.Hom_def 
        chaos_def)
  have "c = chaos \<iinter> c" by simp
  also have "... = inv UNIV \<iinter> c" using inv_chaos by simp
  also have "... \<ge> inv p \<iinter> c"
    using conj.sync_mono_left inv_strengthen by auto
  finally show ?thesis .
qed

lemma gen_inv_introduce: "c \<ge> \<box>p \<iinter> c"
proof -
  have a1: "c \<ge> nil ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> c"
    by (metis inv_introduce local.inv_def seq_nil_left)
  have a2: "nil ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> c \<ge> \<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> c"
    using conj.sync_mono_left nil_ref_test seq_mono_left by blast
  show ?thesis
    by (metis a2 dual_order.trans gen_inv_def inv_introduce local.inv_def seq_nil_left)
qed

lemma gen_inv_merge_helper: "\<tau>(p \<inter> q) ; guar\<^sub>\<alpha>((UNIV \<triangleright> p) \<inter> (UNIV \<triangleright> q)) = \<box>(p \<inter> q)"
proof -
  have "\<tau>(p \<inter> q) ; guar\<^sub>\<alpha>((UNIV \<triangleright> p) \<inter> (UNIV \<triangleright> q)) = \<tau>(p \<inter> q) ; guar\<^sub>\<alpha>(UNIV \<triangleright> (p \<inter> q))"
    by (metis inf_commute inf_top_left range_restrict_inter range_restrict_twice)
  then show ?thesis 
    by (metis gen_inv_def_2)
qed

lemma gen_inv_merge_conj: "\<box>p \<iinter> \<box>q = \<box>(p \<inter> q)"
proof -
  have "\<box>p \<iinter> \<box>q = (\<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>) \<iinter> (\<tau>(q) ; \<alpha>(UNIV \<triangleright> q)\<^sup>\<omega>)"
    by (metis gen_inv_def_2 guar\<^sub>\<alpha>_def)
  also have "... = \<tau>(p) ; \<tau>(q) ; (\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> \<alpha>(UNIV \<triangleright> q)\<^sup>\<omega>)"
    using Atomic2_def Atomic_def2 Env_def Pgm_def chaos_def general_atomic.Hom_ref_hom general_atomic_def iter_mono conj.test_nonaborting_sync_test_nonaborting test_seq_test by auto
  also have "... = \<tau>(p \<inter> q) ; (guar\<^sub>\<alpha>(UNIV \<triangleright> p) \<iinter> guar\<^sub>\<alpha>(UNIV \<triangleright> q))"
    by (simp add: test_seq_test guar\<^sub>\<alpha>_def)
  finally show ?thesis
    using gen_inv_merge_helper guar_rely_merge_guar_atomic by auto
qed

lemma gen_inv_merge_parallel: "\<box>p \<parallel> \<box>q = \<box>(p \<inter> q)"
proof -
  have "\<box>p \<parallel> \<box>q = (\<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>) \<parallel> (\<tau>(q) ; \<alpha>(UNIV \<triangleright> q)\<^sup>\<omega>)"
    by (metis gen_inv_def_2 guar\<^sub>\<alpha>_def)
  also have "... = \<tau>(p) ; \<tau>(q) ; (\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<parallel> \<alpha>(UNIV \<triangleright> q)\<^sup>\<omega>)"
    using Atomic2_def Atomic_def2 Env_def Pgm_def chaos_def general_atomic.Hom_ref_hom general_atomic_def iter_mono par.test_nonaborting_sync_test_nonaborting test_seq_test by auto
  also have "... = \<tau>(p \<inter> q) ; (guar\<^sub>\<alpha>(UNIV \<triangleright> p) \<parallel> guar\<^sub>\<alpha>(UNIV \<triangleright> q))"
    by (simp add: test_seq_test guar\<^sub>\<alpha>_def)
  finally show ?thesis
    using gen_inv_merge_helper guar_atomic_merge_parallel by auto
qed 

lemma gen_inv_merge_inf: "\<box>p \<sqinter> \<box>q = \<box>(p \<inter> q)"
proof -
  have "\<box>p \<sqinter> \<box>q = (\<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>) \<sqinter> (\<tau>(q) ; \<alpha>(UNIV \<triangleright> q)\<^sup>\<omega>)"
    by (metis gen_inv_def_2 guar\<^sub>\<alpha>_def)
  also have "... = \<tau>(p) ; \<tau>(q) ; (\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<sqinter> \<alpha>(UNIV \<triangleright> q)\<^sup>\<omega>)"
    using test_inf_eq_seq test_inf_interchange by auto
  also have "... = \<tau>(p \<inter> q) ; (guar\<^sub>\<alpha>(UNIV \<triangleright> p) \<sqinter> guar\<^sub>\<alpha>(UNIV \<triangleright> q))"
    by (simp add: test_seq_test guar\<^sub>\<alpha>_def)
  finally show ?thesis
    using gen_inv_merge_helper guar_atomic_merge_inf by auto
qed 

lemma gen_inv_distrib_test_conj: "\<box>p \<iinter> \<tau>(q) = \<tau>(p \<inter> q)"
proof -
  have "\<box>p \<iinter> \<tau>(q) = \<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> \<tau>(q) ; nil" 
    by (metis gen_inv_def_2 guar\<^sub>\<alpha>_def seq_nil_right)
  also have "... = \<tau>(p) ; \<tau>(q) ; (\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> nil)"
    by (metis Atomic2_def Atomic_def2 Env_def Pgm_def chaos_def chaos_ref_nil conj.test_nonaborting_sync_test_nonaborting general_atomic.Hom_ref_hom general_atomic_def iter_mono test_seq_test)
  finally show ?thesis
    by (metis conj.atomic_iter_sync_nil seq_nil_right general_atomic_def pgm_or_env_atomic test_seq_test)
qed

lemma gen_inv_distrib_test_par: "\<box>p \<parallel> \<tau>(q) = \<tau>(p \<inter> q)"
proof -
  have "\<box>p \<parallel> \<tau>(q) = \<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<parallel> \<tau>(q) ; nil" 
    by (metis gen_inv_def_2 guar\<^sub>\<alpha>_def seq_nil_right)
  also have "... = \<tau>(p) ; \<tau>(q) ; (\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<parallel> nil)"
    by (metis Atomic2_def Atomic_def2 Env_def Pgm_def chaos_def chaos_ref_nil par.test_nonaborting_sync_test_nonaborting general_atomic.Hom_ref_hom general_atomic_def iter_mono test_seq_test)
  finally show ?thesis
    by (metis par.atomic_iter_sync_nil seq_nil_right general_atomic_def pgm_or_env_atomic test_seq_test)
qed

lemma gen_inv_distrib_test_inf: "\<box>p \<sqinter> \<tau>(q) = \<tau>(p \<inter> q)"
proof -
  have "\<box>p \<sqinter> \<tau>(q) = \<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<sqinter> \<tau>(q) ; nil" 
    by (metis gen_inv_def_2 guar\<^sub>\<alpha>_def seq_nil_right)
  also have "... = \<tau>(p) ; \<tau>(q) ; (\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<sqinter> nil)"
    by (metis test_inf_eq_seq test_inf_interchange)
  finally show ?thesis
    by (metis general_atomic_def inf.atomic_iter_sync_nil pgm_or_env_atomic seq_nil_right test_seq_test)
qed

lemma gen_inv_distrib_assert_conj: "\<box>p \<iinter> \<lbrace>q\<rbrace> = \<lbrace>q\<rbrace> ; \<tau>(p)"
  by (metis seq_nil_right conj.assert_command_sync_command gen_inv_distrib_test_conj seq_nil_right test_seq_test test_top)

lemma gen_inv_distrib_assert_par: "\<box>p \<parallel> \<lbrace>q\<rbrace> = \<lbrace>q\<rbrace> ; \<tau>(p)"
  by (metis seq_nil_right par.assert_command_sync_command gen_inv_distrib_test_par seq_nil_right test_seq_test test_top)

lemma gen_inv_distrib_step_pgm: "\<box>p \<iinter> \<pi>(q) = \<pi>((p \<triangleleft> UNIV) \<inter> q \<inter> (UNIV \<triangleright> p))"
proof -
  have "\<box>p \<iinter> \<pi>(q) =  \<tau>(p) ; guar\<^sub>\<alpha> (UNIV \<triangleright> p) \<iinter> \<pi>(q)"
    by (metis gen_inv_def_2)
  also have "... = \<tau>(p) ; (guar\<^sub>\<alpha> (UNIV \<triangleright> p) \<iinter> \<pi>(q))"
    by (metis conj.nonaborting_sync_test_pre_generic env.hom_bot env_conj_pgm local.conj_commute)
  also have "... = \<tau>(p) ; \<pi>(q \<inter> (UNIV \<triangleright> p))"
    by (metis guar_distrib_step_atomic_pgm local.conj_commute pgm_conj_pgm)
  also have "... = \<pi>((p \<triangleleft> UNIV) \<inter> q \<inter> (UNIV \<triangleright> p))"
    by (metis domain_restrict_inter inf_top_left pgm_test_pre)
  finally show ?thesis .
qed

lemma gen_inv_distrib_step_env: "\<box>p \<iinter> \<epsilon>(q) = \<epsilon>((p \<triangleleft> UNIV) \<inter> q \<inter> (UNIV \<triangleright> p))"
proof -
  have "\<box>p \<iinter> \<epsilon>(q) =  \<tau>(p) ; guar\<^sub>\<alpha> (UNIV \<triangleright> p) \<iinter> \<epsilon>(q)"
    by (metis gen_inv_def_2)
  also have "... = \<tau>(p) ; (guar\<^sub>\<alpha> (UNIV \<triangleright> p) \<iinter> \<epsilon>(q))"
    by (metis conj.nonaborting_sync_test_pre_generic local.conj.right_idem local.conj_commute pgm_conj_env)
  also have "... = \<tau>(p) ; \<epsilon>(q \<inter> (UNIV \<triangleright> p))"
    by (metis env_conj_env guar_distrib_step_atomic_env local.conj_commute)
  also have "... = \<epsilon>((p \<triangleleft> UNIV) \<inter> q \<inter> (UNIV \<triangleright> p))"
    by (metis domain_restrict_inter inf_top_left env_test_pre)
  finally show ?thesis .
qed

lemma gen_inv_distrib_step_atomic: "\<box>p \<iinter> \<alpha>(q) = \<alpha>((p \<triangleleft> UNIV) \<inter> q \<inter> (UNIV \<triangleright> p))"
proof -
  have "\<box>p \<iinter> \<alpha>(q) =  \<tau>(p) ; guar\<^sub>\<alpha> (UNIV \<triangleright> p) \<iinter> \<alpha>(q)"
    by (metis gen_inv_def_2)
  also have "... = \<tau>(p) ; (guar\<^sub>\<alpha> (UNIV \<triangleright> p) \<iinter> \<alpha>(q))"
    by (metis (no_types, lifting) atomic_pull_test conj.sync_nondet_distrib gen_inv_def_2 general_atomic.hom_iso_eq general_atomic_def gen_inv_distrib_step_env gen_inv_distrib_step_pgm seq_assoc test_conj_distrib test_seq_idem)
  also have "... = \<tau>(p) ; \<alpha>(q \<inter> (UNIV \<triangleright> p))"
    by (metis env.hom_iso_eq env_conj_env guar_distrib_step_atomic_atomic local.conj_commute)
  also have "... = \<alpha>((p \<triangleleft> UNIV) \<inter> q \<inter> (UNIV \<triangleright> p))"
    by (metis atomic_pull_test inf_assoc)
  finally show ?thesis .
qed

lemma gen_inv_distrib_Nondet_conj: "\<box>p \<iinter> (\<Squnion>D) = (\<Squnion>d \<in> D. \<box>p \<iinter> d)"
  by (metis conj.non_aborting_distrib conj.test_sync_atomic_pre gen_inv_distrib_test_conj local.conj_assoc)

lemma gen_inv_distrib_Nondet_par: "\<box>p \<parallel> (\<Squnion>D) = (\<Squnion>d \<in> D. \<box>p \<parallel> d)"
  by (metis par.non_aborting_distrib par.test_sync_atomic_pre gen_inv_distrib_test_par local.par_assoc)

lemma guarded_inv:      
  "\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) = \<tau>(p);(\<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p)\<^sup>\<omega>)"
proof -
  have "-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p \<supseteq> (p \<triangleleft> UNIV) \<inter> UNIV \<triangleright> p" by auto
  then have "\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) \<ge> \<tau>(p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>"
    by (simp add: iter_mono seq_mono_right)
  also have "... \<ge> \<tau>(p);(\<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p)\<^sup>\<omega>)"
    by (simp add: iter_mono le_infI2 seq_mono_right)
  then have left_right:"\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) \<ge> \<tau>(p);(\<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p)\<^sup>\<omega>)".
  have helper: "nil \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p);\<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega> \<ge> \<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>"
  proof -
    have "nil \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p);\<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega> \<ge> 
        \<tau>(p) \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> (-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p));\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>" (is "_ \<ge> ?rhs")
    proof -
      have absorb: "\<And>r p. \<alpha>(r \<inter> (UNIV \<triangleright> p));\<tau>(p) = \<alpha>(r \<inter> (UNIV \<triangleright> p))" 
        by (metis general_atomic_test_post inf_top.left_neutral restrict_range_def)
      have negate: "p \<triangleleft> UNIV \<inter> (-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p) = p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p"
        by (simp add: inf_sup_distrib1)
      have "nil \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p);\<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega> \<ge> 
              \<tau>(p) \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p);\<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>" (is "_ \<ge> ?rhs")
        using nil_ref_test sup.mono by fastforce
      also have "?rhs = \<tau>(p) \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> (-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p));\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>"
        using absorb negate by auto
      finally show ?thesis.
    qed
    also have "?rhs = \<tau>(p) \<squnion> \<tau>(p) ; \<alpha>(- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p);\<alpha> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p)\<^sup>\<omega>"
      using atomic_pull_test by presburger
    also have "... = \<tau>(p);(nil \<squnion> \<alpha>(- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p);\<alpha> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p)\<^sup>\<omega>)"
      using par.seq_nondet_distrib seq_assoc seq_nil_right by presburger
    also have "... = \<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>"
      using iter_unfold by auto
    finally show ?thesis.
  qed
  then have right_left: "\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) \<le> \<tau>(p);(\<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p)\<^sup>\<omega>)"
    using iter_induct_nil seq_assoc test_seq_refine by auto 
  finally show ?thesis using right_left left_right by auto
qed

lemma guarded_inv2: "\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) = \<tau>(p);inv(p)"
  by (metis general_atomic_test_post atomic_pull_test guarded_inv local.inv_def par.iter_leapfrog seq_assoc test_seq_idem)

lemma inv_preserve: "\<tau>(p);(inv p) = \<tau>(p);(inv p);\<tau>(p)"
proof -
  have "\<tau>(p);(inv p) = \<tau>(p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>" unfolding inv_def by simp
  also have "... = \<tau>(p);(\<alpha>(UNIV \<triangleright> p);\<tau>(p))\<^sup>\<omega>" using general_atomic_test_post by auto
  also have "... = (\<tau>(p);\<alpha>(UNIV \<triangleright> p))\<^sup>\<omega> ; \<tau>(p) ; \<tau>(p)"
    using par.iter_leapfrog test_seq_idem seq_assoc by auto
  also have "... = \<tau>(p);(\<alpha>(UNIV \<triangleright> p) ; \<tau>(p))\<^sup>\<omega> ; \<tau>(p)"
    using par.iter_leapfrog by auto
  also have "... = \<tau>(p);(inv p);\<tau>(p)" using general_atomic_test_post inv_def by auto
  finally show ?thesis .
qed

lemma gen_inv_seq_gen_inv:
  shows "\<box>p = \<box>p ; \<box>p"
proof -
  have "\<box>p = \<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>"
    by (metis gen_inv_def inv_def)
  also have "... = \<tau>(p) ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> ; \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>"
    by (simp add: seq_assoc)
  also have "... = \<tau>(p) ; inv p ; \<tau>(p) ; inv p"
    by (metis inv_preserve local.inv_def)
  also have "... = \<box>p ; \<box>p"
    by (metis local.gen_inv_def seq_assoc)
  finally show ?thesis .
qed

lemma gen_inv_distrib_seq_conj:
  assumes "\<tau>(-p) ; c \<le> Atomic ; \<top>"
  shows "\<box>p \<iinter> c ; d = (\<box>p \<iinter> c) ; (\<box>p \<iinter> d)"
proof -
  have test_preserve: "\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p) ; \<tau> p = \<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)"
    using atomic_general_atomic general_atomic_test_post seq_assoc by auto
  have "\<box>p \<iinter> c ; d = \<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> c ; d"
    by (metis atomic_general_atomic gen_inv_def_2 guar\<^sub>\<alpha>_def)
  also have "... = (\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> c) ; (\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> d)"
    by (simp add: assms conj.test_atomic_iter_distrib_seq test_preserve)
  finally show ?thesis
    by (metis atomic_general_atomic gen_inv_def_2 guar\<^sub>\<alpha>_def)
qed

lemma gen_inv_distrib_seq_par:
  assumes "\<tau>(-p) ; c \<le> Atomic ; \<top>"
  shows "\<box>p \<parallel> c ; d = (\<box>p \<parallel> c) ; (\<box>p \<parallel> d)"
proof -
  have test_preserve: "\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p) ; \<tau> p = \<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)"
    using atomic_general_atomic general_atomic_test_post seq_assoc by auto
  have "\<box>p \<parallel> c ; d = \<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<parallel> c ; d"
    by (metis atomic_general_atomic gen_inv_def_2 guar\<^sub>\<alpha>_def)
  also have "... = (\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<parallel> c) ; (\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<parallel> d)"
    by (simp add: assms par.test_atomic_iter_distrib_seq test_preserve)
  finally show ?thesis
    by (metis atomic_general_atomic gen_inv_def_2 guar\<^sub>\<alpha>_def)
qed

lemma gen_inv_distrib_fixed_iter_conj:
  assumes "\<tau>(-p) ; c \<le> Atomic ; \<top>"
  assumes "i > 0"
  shows "\<box>p \<iinter> (c \<^sup>;^ i) = (\<box>p \<iinter> c) \<^sup>;^ i"
proof - 
  have induct: "\<forall>j. \<box>p \<iinter> (c \<^sup>;^ Suc j) = (\<box>p \<iinter> c) \<^sup>;^ Suc j"
  proof -
    {
      fix j
      have induct2: "\<box>p \<iinter> (c \<^sup>;^ Suc j) = (\<box>p \<iinter> c) \<^sup>;^ Suc j"
      proof (induct j)
        case 0
        show ?case
          by simp
      next
        case (Suc j)
        have "\<box>p \<iinter> (c \<^sup>;^ Suc (Suc j)) = \<box>p \<iinter> (c ; (c \<^sup>;^ (Suc j)))"
          by simp
        also have "... = (\<box>p \<iinter> c) ; (\<box>p \<iinter> (c \<^sup>;^ (Suc j)))"
          by (simp add: assms(1) gen_inv_distrib_seq_conj)
        finally show ?case
          using Suc.hyps by auto
      qed
    }
    then show ?thesis 
      by (rule allI)
  qed
  show ?thesis
    using assms(2) gr0_implies_Suc induct by blast
qed

lemma gen_inv_distrib_fixed_iter_par:
  assumes "\<tau>(-p) ; c \<le> Atomic ; \<top>"
  assumes "i > 0"
  shows "\<box>p \<parallel> (c \<^sup>;^ i) = (\<box>p \<parallel> c) \<^sup>;^ i"
proof - 
  have induct: "\<forall>j. \<box>p \<parallel> (c \<^sup>;^ Suc j) = (\<box>p \<parallel> c) \<^sup>;^ Suc j"
  proof -
    {
      fix j
      have induct2: "\<box>p \<parallel> (c \<^sup>;^ Suc j) = (\<box>p \<parallel> c) \<^sup>;^ Suc j"
      proof (induct j)
        case 0
        show ?case
          by simp
      next
        case (Suc j)
        have "\<box>p \<parallel> (c \<^sup>;^ Suc (Suc j)) = \<box>p \<parallel> (c ; (c \<^sup>;^ (Suc j)))"
          by simp
        also have "... = (\<box>p \<parallel> c) ; (\<box>p \<parallel> (c \<^sup>;^ (Suc j)))"
          by (simp add: assms(1) gen_inv_distrib_seq_par)
        finally show ?case
          using Suc.hyps by auto
      qed
    }
    then show ?thesis 
      by (rule allI)
  qed
  show ?thesis
    using assms(2) gr0_implies_Suc induct by blast
qed

lemma gen_inv_distrib_finite_iter_plus_conj:
  assumes "\<tau>(-p) ; c \<le> Atomic ; \<top>"
  shows "\<box>p \<iinter> (c ; c\<^sup>\<star>) = (\<box>p \<iinter> c) ; (\<box>p \<iinter> c)\<^sup>\<star>"
proof -     
  define f where f_def: "f \<equiv> \<lambda>i. c \<^sup>;^ i" 
  have "\<box>p \<iinter> (c ; c\<^sup>\<star>) = \<box>p \<iinter> (\<Squnion>i\<in>{i. 0 < i}. f(i))"
    by (simp add: par.fiter_seq_choice_nonempty f_def)
  also have "... = (\<Squnion>i\<in>{i. 0 < i}. \<box>p \<iinter> f(i))"
    by (metis conj.non_aborting_distrib2 gen_inv_distrib_test_conj test.hom_inf test_inf_eq_seq test_seq_compl test_seq_magic)
  also have "... = (\<Squnion>i\<in>{i. 0 < i}. \<box>p \<iinter> (c \<^sup>;^ i))"
    by (simp add: f_def)
  also have "... = (\<Squnion>i\<in>{i. 0 < i}. (\<box>p \<iinter> c) \<^sup>;^ i)"
    using gen_inv_distrib_fixed_iter_conj assms by auto
  finally show ?thesis
    by (simp add: par.fiter_seq_choice_nonempty)
qed

lemma gen_inv_distrib_finite_iter_plus_par:
  assumes "\<tau>(-p) ; c \<le> Atomic ; \<top>"
  shows "\<box>p \<parallel> (c ; c\<^sup>\<star>) = (\<box>p \<parallel> c) ; (\<box>p \<parallel> c)\<^sup>\<star>"
proof -     
  define f where f_def: "f \<equiv> \<lambda>i. c \<^sup>;^ i" 
  have "\<box>p \<parallel> (c ; c\<^sup>\<star>) = \<box>p \<parallel> (\<Squnion>i\<in>{i. 0 < i}. f(i))"
    by (simp add: par.fiter_seq_choice_nonempty f_def)
  also have "... = (\<Squnion>i\<in>{i. 0 < i}. \<box>p \<parallel> f(i))"
    by (metis par.non_aborting_distrib2 gen_inv_distrib_test_par test.hom_inf test_inf_eq_seq test_seq_compl test_seq_magic)
  also have "... = (\<Squnion>i\<in>{i. 0 < i}. \<box>p \<parallel> (c \<^sup>;^ i))"
    by (simp add: f_def)
  also have "... = (\<Squnion>i\<in>{i. 0 < i}. (\<box>p \<parallel> c) \<^sup>;^ i)"
    using gen_inv_distrib_fixed_iter_par assms by auto
  finally show ?thesis
    by (simp add: par.fiter_seq_choice_nonempty)
qed

lemma gen_inv_distrib_finite_iter_conj:
  assumes "\<tau>(-p) ; c \<le> Atomic ; \<top>"
  shows "\<box>p \<iinter> c\<^sup>\<star> = (\<box>p \<iinter> c)\<^sup>\<star> ; \<tau> p"
proof -
  have "\<box>p \<iinter> c\<^sup>\<star> = (\<box>p \<iinter> nil) \<squnion> (\<box>p \<iinter> (c ; c\<^sup>\<star>))"
    by (metis conj.sync_nondet_distrib fiter_unfold)
  also have "... = (\<box>p \<iinter> nil) \<squnion> (\<box>p ; \<tau> p \<iinter> (c ; c\<^sup>\<star>))"
    by (metis inv_preserve_test)
  also have "... = \<tau> p \<squnion> (\<box>p ; \<tau> p \<iinter> (c ; c\<^sup>\<star>))"
    by (metis gen_inv_distrib_test_conj conj.test_sync_post inv_preserve_conj seq_nil_left test_seq_idem test_seq_test)
  also have "... = \<tau> p \<squnion> (\<box>p \<iinter> c) ; (\<box>p \<iinter> c)\<^sup>\<star> ; \<tau> p"
    by (metis assms gen_inv_distrib_finite_iter_plus_conj inv_preserve_conj inv_preserve_test)
  also have "... = (nil \<squnion> (\<box>p \<iinter> c) ; (\<box>p \<iinter> c)\<^sup>\<star>) ; \<tau> p"
    by (simp add: nondet_seq_distrib)
  finally show ?thesis
    by (metis fiter_unfold)
qed

lemma gen_inv_distrib_finite_iter_par:
  assumes "\<tau>(-p) ; c \<le> Atomic ; \<top>"
  shows "\<box>p \<parallel> c\<^sup>\<star> = (\<box>p \<parallel> c)\<^sup>\<star> ; \<tau> p"
proof -
  have "\<box>p \<parallel> c\<^sup>\<star> = (\<box>p \<parallel> nil) \<squnion> (\<box>p \<parallel> (c ; c\<^sup>\<star>))"
    by (metis par.sync_nondet_distrib fiter_unfold)
  also have "... = (\<box>p \<parallel> nil) \<squnion> (\<box>p ; \<tau> p \<parallel> (c ; c\<^sup>\<star>))"
    by (metis inv_preserve_test)
  also have "... = \<tau> p \<squnion> (\<box>p ; \<tau> p \<parallel> (c ; c\<^sup>\<star>))"
    using gen_inv_def gen_inv_distrib_test_par par.nil_sync_test_pre par_commute test_par_distrib by auto
  also have "... = \<tau> p \<squnion> (\<box>p \<parallel> c) ; (\<box>p \<parallel> c)\<^sup>\<star> ; \<tau> p"
    by (simp add: assms gen_inv_distrib_finite_iter_plus_par par.test_sync_post par_commute)
  also have "... = (nil \<squnion> (\<box>p \<parallel> c) ; (\<box>p \<parallel> c)\<^sup>\<star>) ; \<tau> p"
    by (simp add: nondet_seq_distrib)
  finally show ?thesis
    by (metis fiter_unfold)
qed

lemma gen_inv_distrib_iter_conj:
  assumes "c \<le> Atomic ; \<top>"
  shows "\<box>p \<iinter> c\<^sup>\<omega> = (\<box>p \<iinter> c)\<^sup>\<omega> ; \<tau> p"
proof -
  have a1: "\<tau>(-p) ; c \<le> Atomic ; \<top>"
    by (metis assms inf.order_iff test_inf_interchange2)
  have c_inf: "(\<box>p \<iinter> c\<^sup>\<infinity>) = (\<box>p \<iinter> c)\<^sup>\<infinity>"
  proof -
    have test_preserving: "atomic(UNIV \<triangleright> p, UNIV \<triangleright> p) = atomic(UNIV \<triangleright> p, UNIV \<triangleright> p) ; \<tau> p"
      by (metis atomic_general_atomic general_atomic_test_post)
    have "(\<box>p \<iinter> c\<^sup>\<infinity>) = (\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> c\<^sup>\<infinity>)"
      by (metis atomic_general_atomic gen_inv_def_2 guar\<^sub>\<alpha>_def)
    also have "... = (\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> c)\<^sup>\<infinity>"
      by (metis assms conj.atomic_inv_distrib_inf_iter test_preserving)
    finally show ?thesis
      by (metis atomic_general_atomic gen_inv_def_2 guar\<^sub>\<alpha>_def)
  qed

  have "\<box>p \<iinter> c\<^sup>\<omega> = (\<box>p \<iinter> c\<^sup>\<star>) \<squnion> (\<box>p \<iinter> c\<^sup>\<infinity>)"
    by (simp add: conj.sync_nondet_distrib par.iter_isolation)
  also have "... = (\<box>p \<iinter> c)\<^sup>\<star> ; \<tau> p \<squnion> (\<box>p \<iinter> c)\<^sup>\<infinity>"
    by (metis gen_inv_distrib_finite_iter_conj a1 c_inf)
  finally show ?thesis
    by (metis par.iter_isolate)
qed

lemma gen_inv_distrib_iter_par:
  assumes "c \<le> Atomic ; \<top>"
  shows "\<box>p \<parallel> c\<^sup>\<omega> = (\<box>p \<parallel> c)\<^sup>\<omega> ; \<tau> p"
proof -
  have a1: "\<tau>(-p) ; c \<le> Atomic ; \<top>"
    by (metis assms inf.order_iff test_inf_interchange2)
  have c_inf: "(\<box>p \<parallel> c\<^sup>\<infinity>) = (\<box>p \<parallel> c)\<^sup>\<infinity>"
  proof -
    have test_preserving: "atomic(UNIV \<triangleright> p, UNIV \<triangleright> p) = atomic(UNIV \<triangleright> p, UNIV \<triangleright> p) ; \<tau> p"
      by (metis atomic_general_atomic general_atomic_test_post)
    have "(\<box>p \<parallel> c\<^sup>\<infinity>) = (\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<parallel> c\<^sup>\<infinity>)"
      by (metis atomic_general_atomic gen_inv_def_2 guar\<^sub>\<alpha>_def)
    also have "... = (\<tau> p ; atomic(UNIV \<triangleright> p, UNIV \<triangleright> p)\<^sup>\<omega> \<parallel> c)\<^sup>\<infinity>"
      by (metis assms par.atomic_inv_distrib_inf_iter test_preserving)
    finally show ?thesis
      by (metis atomic_general_atomic gen_inv_def_2 guar\<^sub>\<alpha>_def)
  qed

  have "\<box>p \<parallel> c\<^sup>\<omega> = (\<box>p \<parallel> c\<^sup>\<star>) \<squnion> (\<box>p \<parallel> c\<^sup>\<infinity>)"
    by (simp add: par.sync_nondet_distrib par.iter_isolation)
  also have "... = (\<box>p \<parallel> c)\<^sup>\<star> ; \<tau> p \<squnion> (\<box>p \<parallel> c)\<^sup>\<infinity>"
    by (metis gen_inv_distrib_finite_iter_par a1 c_inf)
  finally show ?thesis
    by (metis par.iter_isolate)
qed

lemma inv_maintain: "\<tau>(p);(inv p \<iinter> c) = \<tau>(p);(inv p \<iinter> c);\<tau>(p)"
proof -
  have a: "\<tau>(p);(inv p \<iinter> c) = \<tau>(p);inv p \<iinter> \<tau>(p);c"
    using test_conj_distrib by simp
  also have b: "... = \<tau>(p);(inv p);\<tau>(p) \<iinter> \<tau>(p);c"
    using inv_preserve by auto
  also have "... = (\<tau>(p);(inv p) \<iinter> \<tau>(p);c);\<tau>(p)"
    using conj.test_sync_post local.conj_commute by simp
  also have c: "... = \<tau>(p);(inv p \<iinter> c);\<tau>(p)" using a by simp
  finally show ?thesis .
qed

lemma inv_distrib_Nondet: "inv p \<iinter> (\<Squnion>C) = (\<Squnion>c \<in> C. (inv p \<iinter> c))" 
  using conj_Nondet_distrib_nonaborting inv_introduce by force

lemma inv_distrib_nondet: "inv p \<iinter> (c \<squnion> d) = (inv p \<iinter> c) \<squnion> (inv p \<iinter> d)"
  using conj.sync_nondet_distrib by simp

lemma inv_distrib_seq: "inv p \<iinter> (c ; d) = (inv p \<iinter> c) ; (inv p \<iinter> d)"
proof -
  have "inv p \<iinter> (c ; d) \<ge> (inv p \<iinter> c) ; (inv p \<iinter> d)"
    using iter_seq_iter local.inv_def seq_conj_interchange by metis
  moreover have "(inv p \<iinter> c) ; (inv p \<iinter> d) \<ge> inv p \<iinter> (c ; d) "
     sorry
  ultimately show ?thesis by simp
qed

lemma general_distrib_conj: "a\<^sup>\<omega> \<iinter> (c \<iinter> d) = (a\<^sup>\<omega> \<iinter> c) \<iinter> (a\<^sup>\<omega> \<iinter> d)"
  using conj_conj_distrib_left by auto

lemma inv_distrib_test: "inv p \<iinter> \<tau>(p\<^sub>1) = \<tau>(p\<^sub>1)"
  by (metis (no_types, lifting) conj.sync_nondet_distrib conj.test_sync_nil inv_introduce iter0
      le_iff_sup local.conj_commute local.inv_def sup.order_iff)

lemma inv_distrib_assert: "inv p \<iinter> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis conj.nil_sync_assert inv_distrib_test local.conj_assoc test_sequential_pre.test_top 
      test_sequential_pre_axioms)

lemma inv_distrib_pgm: "inv p \<iinter> \<pi>(r) = \<pi>(r \<triangleright> p)"
proof -
  have "inv p \<iinter> \<pi>(r) = (\<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<squnion> nil) \<iinter> \<pi>(r)"
    unfolding inv_def using iter_unfold sup.commute by metis
  also have "... = \<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> \<pi>(r) \<squnion> nil \<iinter> \<pi>(r)"
    by (simp add: conj.nondet_sync_distrib)
  also have "... = \<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> atomic(r, \<bottom>) \<squnion> nil \<iinter> \<pi>(r)" 
    using atomic_def by auto
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> atomic(r, \<bottom>) \<squnion> nil \<iinter> \<pi>(r)" 
    using seq_iter_conj atomic_general_atomic by metis
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<pi>(r) \<squnion> nil \<iinter> \<pi>(r)" using atomic_def
    by simp
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<pi>(r) \<squnion> \<bottom>"
    by (metis conj.nil_sync_atomic_pre pgm_atomic seq_nil_right)
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<pi>(r)" by auto
  also have "... = \<pi>(r \<triangleright> p)"
    by (simp add: general_atomic_def conj.sync_nondet_distrib local.conj_commute pgm_conj_env pgm_conj_pgm restrict_range_def)
  finally show ?thesis.
qed

lemma inv_distrib_env: "inv p \<iinter> \<epsilon>(r) = \<epsilon>(r \<triangleright> p)"
proof -
  have "inv p \<iinter> \<epsilon>(r) = (\<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<squnion> nil) \<iinter> \<epsilon>(r)"
    unfolding inv_def using iter_unfold sup.commute by metis
  also have "... = \<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> \<epsilon>(r) \<squnion> nil \<iinter> \<epsilon>(r)"
    by (simp add: conj.nondet_sync_distrib)
  also have "... = \<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> atomic(\<bottom>, r) \<squnion> nil \<iinter> \<epsilon>(r)"
    using atomic_def by auto
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> atomic(\<bottom>, r) \<squnion> nil \<iinter> \<epsilon>(r)"
    using seq_iter_conj atomic_general_atomic by metis
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<epsilon>(r) \<squnion> nil \<iinter> \<epsilon>(r)" unfolding atomic_def by simp
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<epsilon>(r) \<squnion> \<bottom>"
    by (metis conj.nil_sync_atomic_pre env_atomic seq_nil_right)
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<epsilon>(r)" by auto
  also have "... = \<epsilon>(r \<triangleright> p)"
    by (simp add: general_atomic_def inf_commute pgmenv_conj_env restrict_range_def)
  finally show ?thesis.
qed

lemma inv_distrib_atomic: "inv p \<iinter> \<alpha>(r) = \<alpha>(r \<triangleright> p)"
  using inv_distrib_pgm inv_distrib_env by (simp add: general_atomic_def conj.sync_nondet_distrib)

lemma inv_distrib_lfp:
  assumes monoG: "mono G"
  assumes conj_G_distrib: "\<And>x. (inv p \<iinter> G x = inv p \<iinter> G(inv p \<iinter> x))"
  shows "inv p \<iinter> lfp G = lfp (\<lambda>x. inv p \<iinter> G x)"
proof -
  have nonaborting: "chaos \<ge> inv p"
    by (metis conj_chaos inv_introduce)
  show ?thesis using Conjunction.conj_distrib.conj_lfp_distrib nonaborting monoG conj_G_distrib
    using conj_distrib_axioms by blast
qed

(*
lemma inv_distrib_gfp: 
  assumes monoG: "mono G"
  assumes conj_G_distrib: "\<And>x. (inv p \<iinter> G x = inv p \<iinter> G(inv p \<iinter> x))"
  shows "inv p \<iinter> gfp G = gfp (\<lambda>x. inv p \<iinter> G x)"
  using conj_gfp_distrib monoG conj_G_distrib
  by blast 
*)

lemma finite_iter_distrib: "inv p \<iinter> c\<^sup>\<star> = (inv p \<iinter> c)\<^sup>\<star>"
proof -
  have H_mono: "mono (\<lambda>x. nil \<squnion> (inv p \<iinter> c);x)"
    unfolding mono_def by (meson nondet_mono_right seq_mono_right)
  have G_mono: "mono (\<lambda>x. nil \<squnion> c;x)"
    unfolding mono_def  by (meson nondet_mono_right seq_mono_right)
  have F_dist: "dist_over_nondet (\<lambda>x. inv p \<iinter> x)"
    by (simp add: inv_distrib_Nondet)
  have comp: "\<And>x. (((\<lambda>x. inv p \<iinter> x) \<circ> (\<lambda>x. nil \<squnion> c;x)) x = 
                ((\<lambda>x. nil \<squnion> (inv p \<iinter> c);x) \<circ> (\<lambda>x. inv p \<iinter> x)) x)"
    apply(auto simp add: comp_def)
    apply(auto simp add: inv_distrib_nondet inv_distrib_seq) (* inv_distrib_seq unproved *)
    using inv_distrib_test by (metis test_sequential_pre.test_top test_sequential_pre_axioms)
  have "(\<lambda>x. inv p \<iinter> x) (lfp (\<lambda>x. nil \<squnion> c;x)) = (lfp (\<lambda>x. nil \<squnion> (inv p \<iinter> c);x))"
    using H_mono G_mono F_dist comp fusion_lfp_eq by blast
  then show ?thesis using fiter_def by simp
qed

(*
lemma iter_distrib: "inv p \<iinter> c\<^sup>\<omega> = (inv p \<iinter> c)\<^sup>\<omega>"
proof -
  have H_mono: "mono (\<lambda>x. nil \<squnion> (inv p \<iinter> c);x)"
    unfolding mono_def by (simp add: seq_mono_right sup.coboundedI2)
  have G_mono: "mono (\<lambda>x. nil \<squnion> c;x)"
    unfolding mono_def by (simp add: seq_mono_right sup.coboundedI2)
  have comp: "\<And>x. (((\<lambda>x. inv p \<iinter> x) \<circ> (\<lambda>x. nil \<squnion> c;x)) x = 
                ((\<lambda>x. nil \<squnion> (inv p \<iinter> c);x) \<circ> (\<lambda>x. inv p \<iinter> x)) x)"
    apply(auto simp add: comp_def)
    apply(auto simp add: inv_distrib_nondet inv_distrib_seq) (* inv_distrib_seq unproved *)
    using inv_distrib_test by (metis test_sequential_pre.test_top test_sequential_pre_axioms)
  have "(\<lambda>x. inv p \<iinter> x) (gfp (\<lambda>x. nil \<squnion> c;x)) = (gfp (\<lambda>x. nil \<squnion> (inv p \<iinter> c);x))"
    using H_mono G_mono inv_dist_over_Inf comp fusion_gfp_eq by blast
  then show ?thesis using iter_def by simp
qed
*)

lemma atomic_par_conj: "\<And>c. \<alpha>(r)\<^sup>\<omega> \<iinter> c = \<epsilon>(r)\<^sup>\<omega> \<parallel> c" sorry

lemma promise_distrib:
  "\<alpha>(r)\<^sup>\<omega> \<iinter> (c \<parallel> d) = (\<alpha>(r)\<^sup>\<omega> \<iinter> c) \<parallel> (\<alpha>(r)\<^sup>\<omega> \<iinter> d)"
proof -
  have "\<alpha>(r)\<^sup>\<omega> \<iinter> (c \<parallel> d) = \<epsilon>(r)\<^sup>\<omega> \<parallel> (c \<parallel> d)"
    using atomic_par_conj by simp
  also have "... = \<epsilon>(r)\<^sup>\<omega> \<parallel> \<epsilon>(r)\<^sup>\<omega> \<parallel> c \<parallel> d"
  proof -
    have "\<epsilon>(r)\<^sup>\<omega> \<parallel> (c \<parallel> d) = (\<epsilon>(r) \<parallel> \<epsilon>(r))\<^sup>\<omega> \<parallel> (c \<parallel> d)"
      using env_par_env_axiom by simp
    also have "... = \<epsilon>(r)\<^sup>\<omega> \<parallel> \<epsilon>(r)\<^sup>\<omega> \<parallel> c \<parallel> d"
      by (smt atomic_par_conj calculation conj.comm.left_commute conj.idem local.conj_commute par_assoc)
    finally show ?thesis.
  qed
  also have "... = (\<epsilon>(r)\<^sup>\<omega> \<parallel> c) \<parallel> (\<epsilon>(r)\<^sup>\<omega> \<parallel> d)"
    using par_assoc par_commute by auto
  also have "... = (\<alpha>(r)\<^sup>\<omega> \<iinter> c) \<parallel> (\<alpha>(r)\<^sup>\<omega> \<iinter> d)"
    using atomic_par_conj by simp
  finally show ?thesis .
qed

(*
lemma inv_lib_no_interference:
  assumes "id_set{|x,y|} \<triangleright> p \<subseteq> p \<triangleleft> UNIV"
  shows "E\<^sup>C\<^sub>x(\<tau>(p);(demand (id x) \<iinter> inv p)) \<iinter> demand (id y) \<ge> \<tau>(E\<^sup>S\<^sub>x p);inv(E\<^sup>S\<^sub>x p) \<iinter> demand (id y)"
  sorry
*)

lemma merge_iteration: "(\<pi>(s \<inter> s') \<squnion> \<epsilon>(r \<inter> r'))\<^sup>\<omega> = (\<pi>(s) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<iinter> (\<pi>(s') \<squnion> \<epsilon>(r'))\<^sup>\<omega>"
  by (metis conj.atomic_iter_sync_iter pgm_or_env_atomic pgmenv_conj_pgmenv)

lemma union_helper: "{(s, s'). p(s)} \<union> {(s, s'). p'(s')} = {(s, s'). p(s) \<or> p'(s')}"
  by blast 

lemma inv_lib_constrained_interference:
  assumes "(-((E\<^sup>S\<^sub>x p) \<triangleleft> UNIV)) \<union> UNIV \<triangleright> (E\<^sup>S\<^sub>x p) \<supseteq> (id y)"
  shows "\<tau>(E\<^sup>S\<^sub>x p);(inv(E\<^sup>S\<^sub>x p) \<iinter> demand (id y)) = \<tau>(E\<^sup>S\<^sub>x p);(guar_inv(E\<^sup>S\<^sub>x p) \<iinter> demand (id y))"
proof -
  have "\<tau>(E\<^sup>S\<^sub>x p);(inv(E\<^sup>S\<^sub>x p) \<iinter> demand (id y)) = \<tau>(E\<^sup>S\<^sub>x p);((\<alpha>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p)\<^sup>\<omega>) \<iinter> demand (id y))"
    using guarded_inv2 conj_mono by (simp add: test_conj_distrib)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<alpha>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p)\<^sup>\<omega>) \<iinter> (\<epsilon>(id y) \<squnion> Pgm)\<^sup>\<omega>)"
    using dem_def restrict_def by auto                                                                           
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);(((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> \<epsilon>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p))\<^sup>\<omega>) \<iinter> (\<epsilon>(id y) \<squnion> Pgm)\<^sup>\<omega>)"
    unfolding general_atomic_def by auto
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);(((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> \<epsilon>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p))\<^sup>\<omega>) \<iinter> (\<epsilon>(id y) \<squnion> \<pi>(UNIV))\<^sup>\<omega>)"
    by (simp add: pgm.Hom_def)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>((-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<inter> UNIV) \<squnion> \<epsilon>((-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<inter> (id y))))\<^sup>\<omega>"
    by (metis conj.atomic_iter_sync_iter inf_sup_aci(5) pgm_or_env_atomic pgmenv_conj_pgmenv sup_commute)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> \<epsilon>(id y)))\<^sup>\<omega>"
    using assms by (simp add: inf.absorb_iff2)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>((-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<inter> UNIV) \<squnion> \<epsilon>(UNIV \<inter> (id y))))\<^sup>\<omega>"
    by simp
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> \<epsilon>(UNIV))\<^sup>\<omega> \<iinter> (\<pi>(UNIV) \<squnion> \<epsilon>(id y))\<^sup>\<omega>)"
    using merge_iteration by presburger
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> Env)\<^sup>\<omega> \<iinter> (Pgm \<squnion> \<epsilon>(id y))\<^sup>\<omega>)"
    by (simp add: env.Hom_def pgm.Hom_def)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> Env)\<^sup>\<omega> \<iinter> demand (id y))"
    by (simp add: sup_commute)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);(guar_inv (E\<^sup>S\<^sub>x p) \<iinter> demand (id y))"
  proof -
    have negate_set_helper: "-{(s, s'). s \<in> (E\<^sup>S\<^sub>x p)} = {(s, s'). s \<notin> (E\<^sup>S\<^sub>x p)}"  by blast
    have "\<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> Env)\<^sup>\<omega> \<iinter> demand (id y))
          = \<tau>(E\<^sup>S\<^sub>x p);((guar(-{(s, s'). s \<in> (E\<^sup>S\<^sub>x p)} \<union> {(s, s'). s' \<in> (E\<^sup>S\<^sub>x p)})) \<iinter> demand (id y))"
      by (simp add: restrict_domain_def restrict_range_def)
    also have "... = \<tau>(E\<^sup>S\<^sub>x p);((guar({(s, s'). -(s \<in> (E\<^sup>S\<^sub>x p))} \<union> {(s, s'). s' \<in> (E\<^sup>S\<^sub>x p)})) \<iinter> demand (id y))"
      by (simp add: negate_set_helper)
    also have "... = \<tau>(E\<^sup>S\<^sub>x p);((guar({(s, s'). -(s \<in> (E\<^sup>S\<^sub>x p)) \<or> s' \<in> (E\<^sup>S\<^sub>x p)})) \<iinter> demand (id y))"
      by (simp add: union_helper) 
    also have "... = \<tau>(E\<^sup>S\<^sub>x p);((guar_inv(E\<^sup>S\<^sub>x p)) \<iinter> demand (id y))"
      using guar_inv_def by auto
    finally show ?thesis.
  qed
  finally show ?thesis.
qed

lemma inv_distrib_par: "inv p \<iinter> (c \<parallel> d) = (inv p \<iinter> c) \<parallel> (inv p \<iinter> d)"
  unfolding inv_def using promise_distrib by auto

end

end

