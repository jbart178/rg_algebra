theory DataRefinement
  imports Invariants While_Loop
begin

locale data_refines = invariants + if_statement + while_loop
begin

definition data_refines :: "'a \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<ge>\<^sub>_ _" 50) where
  "data_refines c p d \<equiv> \<tau>(p);(inv p \<iinter> c) \<ge> \<tau>(p);(inv p \<iinter> d)"

lemma dataref_trans :
  assumes "a \<ge>\<^sub>p b"
      and "b \<ge>\<^sub>p c"
    shows "a \<ge>\<^sub>p c"
proof -
  have "\<tau>(p);(inv p \<iinter> a) \<ge> \<tau>(p);(inv p \<iinter> b)" (is "... \<ge> ?rhs")
    using assms(1) data_refines_def by blast
  also have "?rhs \<ge> \<tau>(p);(inv p \<iinter> c)"
    using assms(2) data_refines_def xtrans by blast
  finally show ?thesis
    by (simp add: data_refines_def)
qed

(* Data refining program operators *)


lemma dataref_Nondet:
  assumes "\<forall>d\<in>D. \<exists>c\<in>C. (c \<ge>\<^sub>p d)"
  shows "\<Squnion>C \<ge>\<^sub>p \<Squnion>D"
proof -
  have "\<tau>(p);(inv p \<iinter> (\<Squnion>C)) = (\<Squnion>c\<in>C. \<tau>(p);(inv p \<iinter> c))"
    using inv_distrib_Nondet by (metis Sup_empty empty_is_image par.seq_NONDET_distrib test_seq_magic) 
  also have "... \<ge> (\<Squnion>d\<in>D. \<tau>(p);(inv p \<iinter> d))" (is "... \<ge> ?rhs")
    using assms data_refines_def by (simp add: SUP_mono)
  also have "?rhs = \<tau>(p);(inv p \<iinter> (\<Squnion>D))" 
    using inv_distrib_Nondet by (metis Sup_empty empty_is_image par.seq_NONDET_distrib test_seq_magic)
  finally show ?thesis using data_refines_def by simp
qed

lemma dataref_nondet:
  assumes "c\<^sub>1 \<ge>\<^sub>p d\<^sub>1" and "c\<^sub>2 \<ge>\<^sub>p d\<^sub>2"
  shows "c\<^sub>1 \<squnion> c\<^sub>2 \<ge>\<^sub>p d\<^sub>1 \<squnion> d\<^sub>2"
proof -
  let ?C = "{c\<^sub>1, c\<^sub>2}"
  let ?D = "{d\<^sub>1, d\<^sub>2}"
  have "\<forall>d\<in>?D. \<exists>c\<in>?C. (c \<ge>\<^sub>p d)"
    using assms conj.sync_mono local.data_refines_def seq_mono by auto
  moreover have "\<Squnion>?C \<ge>\<^sub>p \<Squnion>?D"
    using dataref_Nondet calculation by blast
  ultimately show ?thesis by simp
qed

lemma dataref_seq_distrib: "\<tau>(p);(inv p \<iinter> (c;d)) = \<tau>(p);(inv p \<iinter> c);\<tau>(p);(inv p \<iinter> d)"
    using inv_distrib_seq inv_maintain seq_assoc by metis

lemma dataref_seq:
  assumes "c\<^sub>1 \<ge>\<^sub>p d\<^sub>1" and "c\<^sub>2 \<ge>\<^sub>p d\<^sub>2"
  shows "c\<^sub>1;c\<^sub>2 \<ge>\<^sub>p d\<^sub>1;d\<^sub>2"
proof -
  have "\<tau>(p);(inv p \<iinter> c\<^sub>1;c\<^sub>2) = \<tau>(p);(inv p \<iinter> c\<^sub>1);\<tau>(p);(inv p \<iinter> c\<^sub>2)"
    using dataref_seq_distrib by auto
  also have "... \<ge> \<tau>(p);(inv p \<iinter> d\<^sub>1);\<tau>(p);(inv p \<iinter> d\<^sub>2)" (is "_ \<ge> ?rhs")
    using assms data_refines_def seq_assoc seq_mono by metis
  also have "?rhs = \<tau>(p);(inv p \<iinter> d\<^sub>1;d\<^sub>2)"
    using dataref_seq_distrib by auto
  finally show ?thesis using data_refines_def by simp
qed

lemma inv_test_finite_iter: "\<tau>(p);(inv p \<iinter> c)\<^sup>\<star> = \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
proof -
  have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<star> \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
    by (meson fiter_mono seq_mono_left seq_mono_right subsetI test.hom_mono test_seq_refine)
  moreover have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<star> \<le> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
  proof -
    have "(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star> \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
      by (simp add: test_seq_refine)
    moreover have "(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star> \<ge> \<tau>(p) \<squnion> \<tau>(p);(inv p \<iinter> c);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
      using inv_maintain
      by (metis (no_types, lifting) calculation fiter_unfold par.seq_nondet_distrib seq_assoc seq_nil_right test_seq_idem) (* TODO *)

    moreover have "(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star> \<ge> \<tau>(p) \<squnion> \<tau>(p);(inv p \<iinter> c);\<lbrace>p\<rbrace>;(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
      by (metis calculation(2) inv_maintain seq_assoc test_seq_assert)
    moreover have "\<lbrace>p\<rbrace>;(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star> \<ge> nil \<squnion> (inv p \<iinter> c);\<lbrace>p\<rbrace>;(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
      using assert_galois_test calculation(3) seq_assoc test_nondet_distrib by auto
    ultimately show ?thesis
      by (metis assert_galois_test assert_seq_test fiter_induct_nil seq_assoc)
  qed
  ultimately show ?thesis by simp
qed

lemma dataref_finite_iter:
  assumes "c \<ge>\<^sub>p d"
  shows "c\<^sup>\<star> \<ge>\<^sub>p d\<^sup>\<star>"
proof -
  have "\<tau>(p);(inv p \<iinter> c\<^sup>\<star>) = \<tau>(p);(inv p \<iinter> c)\<^sup>\<star>"
    using finite_iter_distrib by simp
  also have "... = \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
    using inv_test_finite_iter by simp
  also have "... \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> d))\<^sup>\<star>" (is "_ \<ge> ?rhs")
    using assms data_refines_def fiter_mono seq_mono_right by simp
  also have "?rhs = \<tau>(p);(inv p \<iinter> d)\<^sup>\<star>"
    using inv_test_finite_iter by simp
  also have "... = \<tau>(p);(inv p \<iinter> d\<^sup>\<star>)"
    using finite_iter_distrib by simp
  finally show ?thesis using data_refines_def by simp
qed

lemma inv_test_iter: "\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> = \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<omega>"
proof -
  have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<omega>"
    by (meson iter_mono order_refl seq_mono_right test_seq_refine)
  moreover have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<le> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<omega>"
  proof -
    have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p);(inv p \<iinter> c)\<^sup>\<omega>"
      by simp
    moreover have "\<tau>(p) \<squnion> \<tau>(p);(inv p \<iinter> c);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p);(inv p \<iinter> c)\<^sup>\<omega>"
      by (metis iter_unfold seq_assoc seq_nil_right test_nondet_distrib_weak)
    moreover have "nil \<squnion> \<tau>(p);(inv p \<iinter> c);\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p);(inv p \<iinter> c)\<^sup>\<omega>"
      using calculation
    proof -
      have "nil \<squnion> \<tau>(p);(inv p \<iinter> c);\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p) \<squnion> \<tau>(p);(inv p \<iinter> c);(inv p \<iinter> c)\<^sup>\<omega>"
        using inv_maintain nil_ref_test sup_mono by fastforce
      then show ?thesis using calculation order_trans by blast
    qed
    ultimately show ?thesis using iter_induct_nil seq_assoc test_seq_refine by auto
  qed                                   
  ultimately show ?thesis by simp
qed

lemma dataref_iter:
  assumes "c \<ge>\<^sub>p d"
  shows "c\<^sup>\<omega> \<ge>\<^sub>p d\<^sup>\<omega>"
proof -
  have "\<tau>(p);(inv p \<iinter> c\<^sup>\<omega>) = \<tau>(p);(inv p \<iinter> c)\<^sup>\<omega>" 
    (* using iter_distrib *) sorry
  also have "... = \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<omega>"
    using inv_test_iter by blast
  also have "... \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> d))\<^sup>\<omega>" (is "_ \<ge> ?rhs")
    using assms iter_mono local.data_refines_def seq_mono_right by simp
  also have "?rhs = \<tau>(p);(inv p \<iinter> d)\<^sup>\<omega>"
    using inv_test_iter by simp
  also have "... = \<tau>(p);(inv p \<iinter> d\<^sup>\<omega>)"
    (* using iter_distrib *) sorry
  finally show ?thesis using data_refines_def by simp
qed

lemma dataref_conj_distrib:
  "\<tau>(p);(inv p \<iinter> (c \<iinter> d)) = (\<tau>(p);(inv p \<iinter> c)) \<iinter> (\<tau>(p);(inv p \<iinter> d))"
proof -
  have "\<tau>(p);(inv p \<iinter> (c \<iinter> d)) = \<tau>(p);((inv p \<iinter> c) \<iinter> (inv p \<iinter> d))"
    using conj_conj_distrib_left by auto
  also have "... = (\<tau>(p);(inv p \<iinter> c)) \<iinter> (\<tau>(p);(inv p \<iinter> d))"
    by (simp add: test_conj_distrib)
  finally show ?thesis.
qed

lemma dataref_conj:
  assumes "c\<^sub>1 \<ge>\<^sub>p d\<^sub>1" and "c\<^sub>2 \<ge>\<^sub>p d\<^sub>2"
  shows "c\<^sub>1 \<iinter> c\<^sub>2 \<ge>\<^sub>p d\<^sub>1 \<iinter> d\<^sub>2"
proof -
  have "\<tau>(p);(inv p \<iinter> (c\<^sub>1 \<iinter> c\<^sub>2)) = \<tau>(p);(inv p \<iinter> c\<^sub>1) \<iinter> \<tau>(p);(inv p \<iinter> c\<^sub>2)"
    using dataref_conj_distrib by auto
  also have "... \<ge> \<tau>(p);(inv p \<iinter> d\<^sub>1) \<iinter> \<tau>(p);(inv p \<iinter> d\<^sub>2)" (is "_ \<ge> ?rhs")
    using assms by (simp add: conj.sync_mono local.data_refines_def)
  also have "?rhs = \<tau>(p);(inv p \<iinter> (d\<^sub>1 \<iinter> d\<^sub>2))"
    using dataref_conj_distrib by simp
  finally show ?thesis using data_refines_def by simp
qed

lemma dataref_par_distrib:
  "\<tau>(p);(inv p \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)) = \<tau>(p);(inv p \<iinter> c\<^sub>1) \<parallel> \<tau>(p);(inv p \<iinter> c\<^sub>2)"
proof -
  have "\<tau>(p);(inv p \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)) = \<tau>(p);((inv p \<iinter> c\<^sub>1) \<parallel> (inv p \<iinter> c\<^sub>2))"
    using inv_distrib_par by simp (* this is listed as promise_distrib in the paper but this is more specific *)
  also have "... = \<tau>(p);(inv p \<iinter> c\<^sub>1) \<parallel> \<tau>(p);(inv p \<iinter> c\<^sub>2)"
    using test_par_distrib by simp
  finally show ?thesis.
qed

lemma dataref_par:
  assumes "c\<^sub>1 \<ge>\<^sub>p d\<^sub>1" and "c\<^sub>2 \<ge>\<^sub>p d\<^sub>2"
  shows "c\<^sub>1 \<parallel> c\<^sub>2 \<ge>\<^sub>p d\<^sub>1 \<parallel> d\<^sub>2"
proof -
  have "\<tau>(p);(inv p \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)) = \<tau>(p);(inv p \<iinter> c\<^sub>1) \<parallel> \<tau>(p);(inv p \<iinter> c\<^sub>2)"
    using dataref_par_distrib by simp
  also have "... \<ge> \<tau>(p);(inv p \<iinter> d\<^sub>1) \<parallel> \<tau>(p);(inv p \<iinter> d\<^sub>2)" (is "_ \<ge> ?rhs")
    using assms by (simp add: local.data_refines_def par.sync_mono)
  also have "?rhs = \<tau>(p);(inv p \<iinter> (d\<^sub>1 \<parallel> d\<^sub>2))"
    using dataref_par_distrib by simp
  finally show ?thesis using data_refines_def by simp
qed

(* Data refining primitive commands *)

lemma dataref_test:
  assumes "p \<inter> p\<^sub>2 \<subseteq> p\<^sub>1"
  shows "(\<tau> p\<^sub>1) \<ge>\<^sub>p (\<tau> p\<^sub>2)"
proof -
  have "p \<inter> p\<^sub>2 \<subseteq> p \<inter> p\<^sub>1"
    using assms by simp
  moreover have "\<tau>(p);\<tau>(p\<^sub>1) \<ge> \<tau>(p);\<tau>(p\<^sub>2)"
    using calculation test.hom_iso test_seq_test by auto
  moreover have "\<tau>(p);(inv p \<iinter> \<tau>(p\<^sub>1)) \<ge> \<tau>(p);(inv p \<iinter> \<tau>(p\<^sub>2))"
    using calculation(2) inv_distrib_test by auto
  ultimately show ?thesis using data_refines_def by simp
qed

corollary dataref_nil: "nil \<ge>\<^sub>p (\<tau> p)"
proof -
  have "nil = \<tau>(UNIV)"
    using nil_def by simp
  also have "... \<ge>\<^sub>p (\<tau> p)"
    using dataref_test by auto
  finally show ?thesis.
qed

lemma dataref_pgm:
  assumes "p \<triangleleft> r\<^sub>2 \<triangleright> p \<subseteq> r\<^sub>1"
  shows "(\<pi> r\<^sub>1) \<ge>\<^sub>p (\<pi> r\<^sub>2)"
proof -
  have "p \<triangleleft> r\<^sub>1 \<triangleright> p \<supseteq> p \<triangleleft> r\<^sub>2 \<triangleright> p"
    using assms restrict_range_def restrict_domain_def
    by (metis (no_types, lifting) Int_left_absorb inf_le2 le_inf_iff)
  moreover have "\<pi>(p \<triangleleft> r\<^sub>1 \<triangleright> p) \<ge> \<pi>(p \<triangleleft> r\<^sub>2 \<triangleright> p)"
    using calculation pgm.hom_mono by blast
  moreover have "\<tau>(p);\<pi>(r\<^sub>1 \<triangleright> p) \<ge> \<tau>(p);\<pi>(r\<^sub>2 \<triangleright> p)"
    by (metis calculation(2) pgm_test_pre restrict_domain_range_assoc)
  moreover have "\<tau>(p);(inv p \<iinter> \<pi>(r\<^sub>1)) \<ge> \<tau>(p);(inv p \<iinter> \<pi>(r\<^sub>2))"
    using calculation(3) inv_distrib_pgm by simp
  ultimately show ?thesis using data_refines_def by simp
qed

lemma dataref_env:
  assumes "p \<triangleleft> r\<^sub>2 \<triangleright> p \<subseteq> r\<^sub>1"
  shows "(\<epsilon> r\<^sub>1) \<ge>\<^sub>p (\<epsilon> r\<^sub>2)"
proof -
  have "p \<triangleleft> r\<^sub>1 \<triangleright> p \<supseteq> p \<triangleleft> r\<^sub>2 \<triangleright> p"
    using assms restrict_range_def restrict_domain_def
    by (metis (no_types, lifting) inf_le1 inf_le2 le_inf_iff) 
  moreover have "\<epsilon>(p \<triangleleft> r\<^sub>1 \<triangleright> p) \<ge> \<epsilon>(p \<triangleleft> r\<^sub>2 \<triangleright> p)"
    using calculation env.hom_mono by blast
  moreover have "\<tau>(p);\<epsilon>(r\<^sub>1 \<triangleright> p) \<ge> \<tau>(p);\<epsilon>(r\<^sub>2 \<triangleright> p)"
    using calculation(2) by (simp add: env_test_pre restrict_domain_range_assoc) 
  moreover have "\<tau>(p);(inv p \<iinter> \<epsilon>(r\<^sub>1)) \<ge> \<tau>(p);(inv p \<iinter> \<epsilon>(r\<^sub>2))"
    using calculation(3) inv_distrib_env by auto
  ultimately show ?thesis using data_refines_def by simp
qed

lemma dataref_atomic:
  assumes "p \<triangleleft> r\<^sub>2 \<triangleright> p \<subseteq> r\<^sub>1"
  shows "(\<alpha> r\<^sub>1) \<ge>\<^sub>p (\<alpha> r\<^sub>2)"
  using dataref_env dataref_pgm by (simp add: assms general_atomic_def dataref_nondet)

corollary dataref_Pgm: "Pgm \<ge>\<^sub>p (\<pi> r)"
  by (simp add: dataref_pgm pgm.Hom_def)

corollary dataref_Env: "Env \<ge>\<^sub>p (\<epsilon> r)"
  by (simp add: dataref_env env.Hom_def)

corollary dataref_Atomic: "Atomic2 \<ge>\<^sub>p (\<alpha> r)"
  by (simp add: general_atomic.Hom_ref_hom conj.sync_mono_right local.data_refines_def seq_mono)

(* Data refining composite commands *)

lemma assert_def_equiv: "\<lbrace>p\<rbrace> = nil \<squnion> \<tau>(-p);\<top>"
  by (smt assert_def seq_abort_right sup.orderE sup_assoc sup_commute test.hom_not test_nondet_compl)

lemma dataref_assert:
  assumes "p \<inter> p\<^sub>1 \<subseteq> p\<^sub>2"
  shows "\<lbrace>p\<^sub>1\<rbrace> \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>"
proof -
  have nil_dref_nil: "nil \<ge>\<^sub>p nil"
    by (simp add: local.data_refines_def) 
  have abort_dref_abort: "\<top> \<ge>\<^sub>p \<top>"
    by (simp add: dataref_iter iter_abort nil_dref_nil) 
  have "\<lbrace>p\<^sub>1\<rbrace> = nil \<squnion> \<tau>(-p\<^sub>1);\<top>" using assert_def_equiv by simp
  also have "... \<ge>\<^sub>p (nil \<squnion> \<tau>(-p\<^sub>2);\<top>)"
  proof -
    have "p \<inter> -p\<^sub>2 \<subseteq> -p\<^sub>1" using assms by blast
    then have "(\<tau>(-p\<^sub>1)) \<ge>\<^sub>p (\<tau>(-p\<^sub>2))" using dataref_test by auto
    then have "(\<tau>(-p\<^sub>1);\<top>) \<ge>\<^sub>p (\<tau>(-p\<^sub>2);\<top>)" using dataref_seq abort_dref_abort by auto
    then have "(nil \<squnion> \<tau>(-p\<^sub>1);\<top>) \<ge>\<^sub>p (nil \<squnion> \<tau>(-p\<^sub>2);\<top>)" using dataref_nondet nil_dref_nil by auto
    then show ?thesis .
  qed
  also have "... = \<lbrace>p\<^sub>2\<rbrace>"
    using assert_def_equiv by auto
  finally show ?thesis.
qed

lemma dataref_guar:
  assumes "p \<triangleleft> g\<^sub>2 \<triangleright> p \<subseteq> g\<^sub>1"
  shows "(guar g\<^sub>1) \<ge>\<^sub>p (guar g\<^sub>2)"
proof -
  have "(\<pi>(g\<^sub>1) \<squnion> Env) \<ge>\<^sub>p (\<pi>(g\<^sub>2) \<squnion> Env)"
    using dataref_nondet dataref_atomic assms dataref_Env dataref_pgm env.Hom_def by auto
  then have "((\<pi>(g\<^sub>1) \<squnion> Env)\<^sup>\<omega>) \<ge>\<^sub>p ((\<pi>(g\<^sub>2) \<squnion> Env)\<^sup>\<omega>)"
    using dataref_iter by simp
  then show ?thesis using guar_def by auto
qed

lemma rely_def2: "rely r = (Pgm \<squnion> Env \<squnion> \<epsilon>(-r);\<top>)\<^sup>\<omega>"
proof -
  have "(Pgm \<squnion> Env \<squnion> \<epsilon>(-r);\<top>)\<^sup>\<omega> = (Pgm \<squnion> \<epsilon>(r) \<squnion> \<epsilon>(-r) \<squnion> \<epsilon>(-r);\<top>)\<^sup>\<omega>"
    by (metis (no_types, lifting) env.Hom_def env.hom_sup sup_assoc sup_compl_top)
  also have "... = ((\<epsilon>(r) \<squnion> Pgm) \<squnion> (atomic.negate(\<epsilon>(r)) \<sqinter> \<E>);\<top>)\<^sup>\<omega>"
    by (smt env_assump_def1 env_assump_def5 inf_sup_aci(5) inf_sup_aci(6) negate_env_sup_Env par.seq_nondet_distrib pgm.Hom_def seq_nil_right sup_top_left)
  finally show ?thesis unfolding rely_def by simp
qed

lemma dataref_rely:
  assumes "p \<triangleleft> r\<^sub>1 \<triangleright> p \<subseteq> r\<^sub>2"
  shows "(rely r\<^sub>1) \<ge>\<^sub>p (rely r\<^sub>2)"
proof -
  have nil_dref_nil: "nil \<ge>\<^sub>p nil"
    by (simp add: local.data_refines_def) 
  have abort_dref_abort: "\<top> \<ge>\<^sub>p \<top>"
    by (simp add: dataref_iter iter_abort nil_dref_nil) 
  have calculation: "p \<triangleleft> (-r\<^sub>2) \<triangleright> p \<subseteq> -r\<^sub>1"
    using assms restrict_range_def restrict_domain_def
  proof -
    have "p \<triangleleft> r\<^sub>1 \<inter> range_restriction p \<inter> r\<^sub>2 = p \<triangleleft> r\<^sub>1 \<triangleright> p"
      by (metis assms inf.orderE restrict_range_def)
    then have "p \<triangleleft> (- r\<^sub>2) \<triangleright> p \<inter> r\<^sub>1 = - r\<^sub>2 \<inter> - r\<^sub>2 \<inter> (p \<triangleleft> r\<^sub>1 \<inter> range_restriction p \<inter> r\<^sub>2)"
      by (simp add: Int_commute inf.left_commute restrict_domain_def restrict_range_def)
    then show ?thesis
      by (simp add: disjoint_eq_subset_Compl)
  qed
  then have "(Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>1);\<top>) \<ge>\<^sub>p (Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>2);\<top>)"
  proof -
    have "(\<epsilon>(-r\<^sub>1);\<top>) \<ge>\<^sub>p (\<epsilon>(-r\<^sub>2);\<top>)"
      using dataref_seq dataref_env calculation abort_dref_abort by auto
    then have "(Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>1);\<top>) \<ge>\<^sub>p (Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>2);\<top>)"
      using dataref_nondet dataref_Pgm dataref_Env by (simp add: env.Hom_def pgm.Hom_def)
    then show ?thesis.
  qed
  then have "((Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>1);\<top>)\<^sup>\<omega>) \<ge>\<^sub>p ((Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>2);\<top>)\<^sup>\<omega>)"
    using dataref_iter by simp
  then show ?thesis using rely_def2 by simp
qed

lemma dataref_term: "term \<ge>\<^sub>p term"
  by (simp add: local.data_refines_def)

lemma restrict_image:
  assumes "s \<in> p"
  shows "q``{s} = (p\<triangleleft>q)``{s}"
  apply(auto simp add:assms restrict_domain_def Image_def)
  done

lemma dataref_spec:
  assumes "p \<inter> p\<^sub>1 \<subseteq> p\<^sub>2"
      and "(p \<inter> p\<^sub>1) \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> q\<^sub>1"
    shows "\<lbrace>p\<^sub>1\<rbrace>;\<lparr>q\<^sub>1\<rparr> \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>;\<lparr>q\<^sub>2\<rparr>"
proof -
  have "(\<forall>s\<in>p\<^sub>1. p \<inter> (p\<^sub>1 \<triangleleft> q\<^sub>2)``{s} \<subseteq> (p\<^sub>1 \<triangleleft> q\<^sub>1)``{s})"
    apply(auto simp add: Image_def restrict_domain_def)
    using assms(2) restrict_domain_def restrict_range_def sorry
  then have calculation: "(\<forall>s\<in>p\<^sub>1. ((\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>1)``{s})) \<ge>\<^sub>p (\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>2)``{s}))))"
    using dataref_test by simp
  then have a: "(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>1)``{s})) \<ge>\<^sub>p (\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>2)``{s}))"
    apply(auto simp add: data_refines_def)
    sorry
  have "\<lbrace>p\<^sub>1\<rbrace>;\<lparr>q\<^sub>1\<rparr> = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
    using old_spec spec_def by presburger
  moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
  proof -
    have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s})) = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
      using assert_seq_test seq_assoc by (metis (no_types, lifting))
    also have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<Squnion>s\<in>UNIV. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))" by simp
    also have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<tau>(UNIV);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s})))"
      using test_restricts_Nondet test_top by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1 \<inter> UNIV);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
      using test_seq_test seq_assoc calculation by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<tau>(p\<^sub>1);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s})))"
      using seq_assoc by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
      using seq_assoc 
      by (simp add: test_restricts_Nondet seq_assoc)
    ultimately show ?thesis by (simp add: assert_seq_test)
  qed
  moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>1)``{s}))"
    using  restrict_image Sup.SUP_cong restrict_domain_def Image_def by smt
  moreover have "... \<ge>\<^sub>p \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>2)``{s}))"
    using a dataref_seq dataref_assert by simp
  moreover have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>2)``{s})) = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
    using  restrict_image Sup.SUP_cong restrict_domain_def Image_def by smt
  moreover have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>2``{s})) = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
  proof -
    have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s})) = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
      using assert_seq_test seq_assoc by (metis (no_types, lifting))
    also have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<Squnion>s\<in>UNIV. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))" by simp
    also have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<tau>(UNIV);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s})))"
      using test_restricts_Nondet test_top by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1 \<inter> UNIV);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
      using test_seq_test seq_assoc calculation by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<tau>(p\<^sub>1);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s})))"
      using seq_assoc by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
      by (simp add: test_restricts_Nondet seq_assoc)
    ultimately show ?thesis by (simp add: assert_seq_test)
  qed
  moreover have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s})) \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>;\<lparr>q\<^sub>2\<rparr>"
    apply(auto simp add: spec_def)
    using dataref_assert assms(1) dataref_seq data_refines_def old_spec spec_def by force
  ultimately show ?thesis using dataref_trans by presburger
qed


lemma dataref_idle:
  assumes "p \<triangleleft> g \<triangleright> p \<subseteq> Id"
  shows "idle \<ge>\<^sub>p (guar g \<iinter> term)"
  using idle_def dataref_conj dataref_term dataref_guar assms by simp


lemma dataref_opt:
  assumes "p \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> q\<^sub>1"
  shows "(opt(q\<^sub>1)) \<ge>\<^sub>p (opt(q\<^sub>2))"
proof -
  have calc: "{\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>2} \<inter> p \<subseteq> {\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>1}"
  proof -
    have "{\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>2} \<inter> p = {\<sigma>. (\<sigma>,\<sigma>)\<in>p \<triangleleft> q\<^sub>2}"
      unfolding restrict_domain_def restrict_range_def by fastforce
    also have "... = {\<sigma>. (\<sigma>,\<sigma>)\<in>p \<triangleleft> q\<^sub>2 \<triangleright> p}"
      by (metis (no_types, lifting) Int_Collect inf_commute restrict_domain_def restrict_range_def split_conv)
    also have "... \<subseteq> {\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>1}"
      using assms by auto
    finally show ?thesis .
  qed 
  have "opt(q\<^sub>1) = \<pi>(q\<^sub>1) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>1})" unfolding opt_def by simp
  also have "... \<ge>\<^sub>p (\<pi>(q\<^sub>2) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>2}))"
    using dataref_nondet dataref_atomic dataref_test calc
    by (metis (no_types, lifting) assms dataref_pgm inf_commute)
  moreover have "(\<pi>(q\<^sub>2) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>2})) = opt(q\<^sub>2)" unfolding opt_def by simp
  ultimately show ?thesis by simp
qed

lemma dataref_atomic_spec:
  assumes "p \<inter> p\<^sub>1 \<subseteq> p\<^sub>2"
      and "(p \<inter> p\<^sub>1) \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> q\<^sub>1"
      and "p \<triangleleft> g \<triangleright> p \<subseteq> Id"
    shows "\<langle>p\<^sub>1, q\<^sub>1\<rangle> \<ge>\<^sub>p ((guar g \<iinter> term);\<lbrace>p\<^sub>2\<rbrace>;opt(q\<^sub>2);(guar g \<iinter> term))"
proof -
  have a: "idle \<ge>\<^sub>p (guar g \<iinter> term)" using assms(3) dataref_idle by simp
  have b: "\<lbrace>p\<^sub>1\<rbrace> \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>"
    by (simp add: assms(1) dataref_assert)
  have "p \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> p\<^sub>1 \<triangleleft> q\<^sub>2"
    using assms(2) restrict_range_def restrict_domain_def sorry
  then have c: "(opt(p\<^sub>1 \<triangleleft> q\<^sub>2)) \<ge>\<^sub>p (opt(q\<^sub>2))"
    using dataref_opt by auto
  have idle_dref_idle: "idle \<ge>\<^sub>p idle"
    by (simp add: local.data_refines_def) 
  have "(p \<inter> p\<^sub>1) \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> p\<^sub>1 \<triangleleft>  q\<^sub>1"
    using assms(2)
    by (metis (no_types, lifting) domain_restrict_twice inf.absorb_iff2 inf_aci(4) 
        inf_commute inf_sup_aci(2) restrict_domain_def restrict_domain_range_assoc) 
  then have opt_dref: "(opt(p\<^sub>1 \<triangleleft> q\<^sub>1)) \<ge>\<^sub>p (opt(p\<^sub>1 \<triangleleft> q\<^sub>2))"
    using dataref_opt by (simp add: domain_restrict_twice) 
  have assert_dref: "\<lbrace>p\<^sub>1\<rbrace> \<ge>\<^sub>p \<lbrace>p\<^sub>1\<rbrace>"
      by (simp add: dataref_assert)
  have "\<langle>p\<^sub>1, p\<^sub>1 \<triangleleft> q\<^sub>1\<rangle> \<ge> \<langle>p\<^sub>1, q\<^sub>1\<rangle>"
    by (simp add: strengthen_spec)
  also have "\<langle>p\<^sub>1, q\<^sub>1\<rangle> \<ge> \<langle>p\<^sub>1, p\<^sub>1 \<triangleleft> q\<^sub>1\<rangle>"
    using strengthen_spec assms atomic_spec_strengthen_post by (simp add: restrict_domain_def) 
  then have "\<langle>p\<^sub>1, q\<^sub>1\<rangle> = \<langle>p\<^sub>1, p\<^sub>1 \<triangleleft> q\<^sub>1\<rangle>" 
    using calculation by auto
  then have w: "\<langle>p\<^sub>1, q\<^sub>1\<rangle> = idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>1);idle"
    using atomic_spec_def by auto
  moreover have "(idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>1);idle) \<ge>\<^sub>p (idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>2);idle)"
    using idle_dref_idle opt_dref dataref_seq calculation assert_dref by simp
  moreover have "(idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>2);idle) \<ge>\<^sub>p ((guar g \<iinter> term);\<lbrace>p\<^sub>2\<rbrace>;opt(q\<^sub>2);(guar g \<iinter> term))"
  proof -
    have "(idle;\<lbrace>p\<^sub>1\<rbrace>) \<ge>\<^sub>p ((guar g \<iinter> term) ;\<lbrace>p\<^sub>2\<rbrace>)"
      using a b dataref_seq by auto
    moreover have "(idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>2)) \<ge>\<^sub>p ((guar g \<iinter> term);\<lbrace>p\<^sub>2\<rbrace>;opt(q\<^sub>2))"
      using calculation c dataref_seq by blast
    moreover have "(idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>2);idle) \<ge>\<^sub>p ((guar g \<iinter> term);\<lbrace>p\<^sub>2\<rbrace>;opt(q\<^sub>2);(guar g \<iinter> term))"
      using calculation(2) dataref_seq a by blast
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis
    using dataref_trans by presburger
qed

lemma dataref_rgspec:
  assumes "p \<inter> p\<^sub>1 \<subseteq> p\<^sub>2"
      and "p \<triangleleft>  r\<^sub>1 \<triangleright> p \<subseteq> r\<^sub>2"
      and "p \<triangleleft> g\<^sub>2 \<triangleright> p \<subseteq> g\<^sub>1"
      and "(p \<inter> p\<^sub>1) \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> q\<^sub>1"
    shows "(rely r\<^sub>1 \<iinter> guar g\<^sub>1 \<iinter> \<lbrace>p\<^sub>1\<rbrace>;\<lparr>q\<^sub>1\<rparr>) \<ge>\<^sub>p (rely r\<^sub>2 \<iinter> guar g\<^sub>2 \<iinter> \<lbrace>p\<^sub>2\<rbrace>;\<lparr>q\<^sub>2\<rparr>)"
proof -
  have "(rely r\<^sub>1 \<iinter> guar g\<^sub>1) \<ge>\<^sub>p (rely r\<^sub>2 \<iinter> guar g\<^sub>2)"
    using dataref_conj dataref_rely dataref_guar assms by auto
  moreover have "\<lbrace>p\<^sub>1\<rbrace>;\<lparr>q\<^sub>1\<rparr> \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>;\<lparr>q\<^sub>2\<rparr>"
    using dataref_spec assms by simp 
  ultimately show ?thesis using dataref_conj by blast
qed

(*
lemma dataref_expr:
  assumes "p \<inter> expr_eq(e\<^sub>1, k) = p \<inter> expr_eq(e\<^sub>2, k)"
      and "single_reference e\<^sub>1 r"
      and "single_reference e\<^sub>2 r"
  shows "(\<lbrakk>e\<^sub>1\<rbrakk>k) \<ge>\<^sub>p (\<lbrakk>e\<^sub>2\<rbrakk>k)"
*)

lemma dataref_conditional:
  assumes "p \<inter> (expr_type b\<^sub>1 boolean) = p \<inter> (expr_type b\<^sub>2 boolean)"
  assumes "single_reference b\<^sub>1 r"
  assumes "single_reference b\<^sub>2 r"
      and "c\<^sub>1 \<ge>\<^sub>p c\<^sub>2" and "d\<^sub>1 \<ge>\<^sub>p d\<^sub>2"
    shows "(if b\<^sub>1 then c\<^sub>1 else d\<^sub>1 fi) \<ge>\<^sub>p (if b\<^sub>2 then c\<^sub>2 else d\<^sub>2 fi)"
proof -
  have "(if b\<^sub>1 then c\<^sub>1 else d\<^sub>1 fi) = (\<lbrakk>b\<^sub>1\<rbrakk>(true);c\<^sub>1 \<squnion> \<lbrakk>b\<^sub>1\<rbrakk>(false);d\<^sub>1);idle \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<^sub>1\<rbrakk>(k);\<top>)"
    unfolding if_statement_def by simp
  moreover have "(\<lbrakk>b\<^sub>1\<rbrakk>(true);c\<^sub>1 \<squnion> \<lbrakk>b\<^sub>1\<rbrakk>(false);d\<^sub>1);idle \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<^sub>1\<rbrakk>(k);\<top>) \<ge>\<^sub>p 
    (\<lbrakk>b\<^sub>2\<rbrakk>(true);c\<^sub>2 \<squnion> \<lbrakk>b\<^sub>2\<rbrakk>(false);d\<^sub>2);idle \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<^sub>2\<rbrakk>(k);\<top>)" sorry
  moreover have "(\<lbrakk>b\<^sub>2\<rbrakk>(true);c\<^sub>2 \<squnion> \<lbrakk>b\<^sub>2\<rbrakk>(false);d\<^sub>2);idle \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<^sub>2\<rbrakk>(k);\<top>) = (if b\<^sub>2 then c\<^sub>2 else d\<^sub>2 fi)"
    unfolding if_statement_def by simp
  ultimately show ?thesis by auto
qed

lemma dataref_gfp:
  assumes "\<And>x. ((G(x)) \<ge>\<^sub>p (F(x)))"
      and "mono G" and "mono F"
      and conj_G_distrib: "\<And>x. (inv p \<iinter> G x = inv p \<iinter> G(inv p \<iinter> x))"
      and conj_F_distrib: "\<And>x. (inv p \<iinter> F x = inv p \<iinter> F(inv p \<iinter> x))"
  shows "(gfp (\<lambda>x. G(x))) \<ge>\<^sub>p (gfp (\<lambda>x. F(x)))"
proof -
  have "\<tau>(p);(inv p \<iinter> gfp (\<lambda>x. G(x))) = \<tau>(p);(gfp (\<lambda>x. inv p \<iinter> G(x)))"
    sorry (* using inv_distrib_gfp seq_mono assms by simp *)
  also have "... = gfp (\<lambda>x. \<tau>(p);(inv p \<iinter> G(x)))" sorry
  also have "... \<ge> gfp (\<lambda>x. \<tau>(p);(inv p \<iinter> F(x)))" (is "... \<ge> ?rhs")
    using assms(1) by (simp add: gfp_mono data_refines_def)
  also have "?rhs = \<tau>(p);(gfp (\<lambda>x. (inv p \<iinter> F(x))))" sorry
  also have "... = \<tau>(p);(inv p \<iinter> gfp (\<lambda>x. F(x)))"
    sorry (* using inv_distrib_gfp seq_mono assms by simp *)
  finally show ?thesis using data_refines_def by blast 
qed

lemma dataref_while:
  assumes "p \<inter> (expr_type b\<^sub>1 boolean) = p \<inter> (expr_type b\<^sub>2 boolean)" and "c\<^sub>1 \<ge>\<^sub>p c\<^sub>2"
  shows "(while b\<^sub>1 do c\<^sub>1 od) \<ge>\<^sub>p (while b\<^sub>2 do c\<^sub>2 od)"
proof -
  have "(while b\<^sub>1 do c\<^sub>1 od) = gfp (\<lambda>x. if b\<^sub>1 then c\<^sub>1;x else nil fi)" 
    unfolding while_statement_def by simp
  moreover have "(gfp (\<lambda>x. if b\<^sub>1 then c\<^sub>1;x else nil fi)) \<ge>\<^sub>p (gfp (\<lambda>x. if b\<^sub>2 then c\<^sub>2;x else nil fi))"
    using dataref_gfp sorry
  moreover have "(gfp (\<lambda>x. if b\<^sub>2 then c\<^sub>2;x else nil fi)) = (while b\<^sub>2 do c\<^sub>2 od)"
    unfolding while_statement_def by simp
  ultimately show ?thesis by simp
qed

lemma dataref:
  assumes "{|x,y|}:\<^sub>s initx \<ge> {|y|}:\<^sub>s inity;\<lbrace>py\<rbrace>;\<tau>(p)"
      and "py \<subseteq> E\<^sup>S\<^sub>x p"
      and "\<lbrace>py\<rbrace>;{|y,x,z|}:\<^sub>s cx \<ge>\<^sub>p \<lbrace>py\<rbrace>;{|y,x,z|}:\<^sub>s dy"
      and "nil \<squnion> Atomic2;\<top> \<ge> \<tau>(py);{|y,x,z|}:\<^sub>s dy"
      and "-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p \<supseteq> id y"
      and "\<lbrace>py\<rbrace>;({|y,z|}:\<^sub>s dy \<iinter> guar_inv(E\<^sup>S\<^sub>x p)) \<ge> \<lbrace>py\<rbrace>;{|y,z|}:\<^sub>s dy" 
    shows "(var x . {|x,z|}:\<^sub>s (initx;cx)) \<ge> (var y . {|y,z|}:\<^sub>s (inity;\<lbrace>py\<rbrace>;dy))"
  sorry

end

end