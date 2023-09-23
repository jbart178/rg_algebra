section \<open>Relies combined with guarantees\<close>

theory Relies_Guarantees
imports
  "Relies"
  "Guarantees"
  "Constrained_Atomic_Commands"
begin

locale relies_guarantees = constrained_atomic + relies + guarantees +
  constrains env  :: "('state \<times> 'state) set \<Rightarrow> 'a"
  constrains pgm  :: "('state \<times> 'state) set \<Rightarrow> 'a"
  constrains test :: "'state set \<Rightarrow> 'a"
begin

lemma rely_guar_def:
  shows "(rely r) \<iinter> (guar g) = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)"
proof -
  have "(rely r) \<iinter> (guar g) = (\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>"
    using rely_def3 guar_def pgm_restrict_def Env_def by simp
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r)) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega>;((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>)"
    using conj.atomic_iter_pre_sync_iter pgm_or_env_atomic by metis
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>)"
    using pgmenv_conj_pgmenv pgmenv_conj_env by presburger
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;(nil \<squnion> (\<epsilon>(-r) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)));\<top>)"
    using conj.atomic_optional_sync_iter pgm_or_env_atomic env_atomic conj_abort_left by metis
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r \<sqinter> \<top>);\<top>)"
    by (metis inf_top.right_neutral inf_top_left local.conj_commute pgmenv_conj_env)
  finally show ?thesis by simp
qed  

lemma rely_guar_stable_step:
  assumes p_stable_under_rg: "stable p (r \<union> g)"
  shows "(\<pi>(g) \<squnion> \<epsilon>(r));\<tau>(p) \<ge> \<tau>(p);(\<pi>(g) \<squnion> \<epsilon>(r))"
proof -
  have "\<pi>(g);\<tau>(p) \<ge> \<tau>(p);\<pi>(g)"
    using pgm_test_ref p_stable_under_rg unfolding stable_def by blast
  moreover have "\<epsilon>(r);\<tau>(p) \<ge> \<tau>(p);\<epsilon>(r)"
      using env_test_ref p_stable_under_rg unfolding stable_def by blast
  ultimately show ?thesis 
    using sup_mono nondet_seq_distrib par.seq_nondet_distrib by simp
qed

(* Lemma 18 *)
lemma rely_guar_stable: 
  assumes p_stable_under_rg: "stable p (r \<union> g)"
  shows "(rely r) \<iinter> (guar g);\<tau>(p) \<ge> (rely r) \<iinter> \<tau>(p);(guar g)"
proof -
  have "(rely r) \<iinter> (guar g);\<tau>(p) \<ge> ((rely r) \<iinter> (guar g));\<tau>(p)" (is "_ \<ge> ?rhs")
    using rely_seq_distrib test_rely_conj conj_commute by metis
  also have "?rhs = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>);\<tau>(p)"
    using rely_guar_def by simp 
  also have "... = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(\<tau>(p) \<squnion> \<epsilon>(-r);\<top>)"
     using nondet_seq_distrib seq_abort seq_assoc by simp
  also have "... \<ge> (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(\<tau>(p) \<squnion> \<tau>(p);\<epsilon>(-r);\<top>)" (is "_ \<ge> ?rhs")
    using seq_mono_right nondet_mono_right seq_mono_left 
          nil_ref_test seq_nil_left by metis
  also have "?rhs = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<tau>(p);(nil \<squnion> \<epsilon>(-r);\<top>)"
    using par.seq_nondet_distrib seq_assoc by simp
  also have "... \<ge> \<tau>(p);(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)" (is "_ \<ge> ?rhs")
    using rely_guar_stable_step iter_test_pre
          seq_mono_left p_stable_under_rg by simp
  also have "?rhs = \<tau>(p);((rely r) \<iinter> (guar g))"
    using rely_guar_def seq_assoc by simp
  also have "... = (rely r) \<iinter> \<tau>(p);(guar g)"
    using test_pre_rely by simp
  finally show ?thesis .
qed

lemma guar_opt: 
  assumes refl: "refl g"
  shows "(guar g) \<iinter> (opt q) = opt(g \<inter> q)"
proof -
  have "(guar g) \<iinter> (opt q) = (\<pi>(g) \<squnion> \<E>)\<^sup>\<omega> \<iinter> (\<pi>(q) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q}))"
    unfolding opt_def guar_def pgm_restrict_def by simp
  also have "... = (nil \<squnion> (\<pi>(g) \<squnion> \<E>);(\<pi>(g) \<squnion> \<E>)\<^sup>\<omega>) \<iinter> (\<pi>(q) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q}))"
    using iter_unfold by simp
  also have "... = \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q}) \<squnion> \<pi>(g \<inter> q)"
  proof -
    obtain ag where b1: "atomic ag = \<pi>(g) \<squnion> \<E>" using pgm_restrict_atomic by (metis pgm_restrict_def)
    obtain aq where b2: "atomic aq = \<pi>(q)" using pgm_atomic by metis
    have b3: "((\<pi>(g) \<squnion> \<E>);(\<pi>(g) \<squnion> \<E>)\<^sup>\<omega> \<iinter> \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q})) = \<bottom>" 
      by (metis (no_types, lifting) b1 conj.atomic_pre_sync_nil conj.atomic_pre_sync_test_pre seq_nil_right test_seq_magic)
    moreover have "nil \<iinter> \<pi>(q) = \<bottom>" using conj.atomic_pre_sync_nil pgm_atomic conj_commute seq_nil_right by metis
    moreover have "(\<pi>(g) \<squnion> \<E>);(\<pi>(g) \<squnion> \<E>)\<^sup>\<omega> \<iinter> \<pi>(q) = \<pi>(g \<inter> q)"  
    proof -
      have "(atomic ag)\<^sup>\<omega> \<iinter> nil = nil" using conj.atomic_iter_sync_nil by simp
      moreover have "(atomic ag) \<iinter> (atomic aq) = \<pi>(g \<inter> q)"
        unfolding b1 b2
        using conj.nondet_sync_distrib local.conj_commute pgm_conj_atomid pgm_conj_pgm by auto
      ultimately show ?thesis using conj.atomic_pre_sync_atomic_pre b1 b2 seq_nil_right by metis
    qed
    moreover have "nil \<iinter> \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q}) = \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q})"
      using conj.sync_commute conj.test_sync_nil by auto
    ultimately show ?thesis using conj.nondet_sync_product by simp
  qed
  also have "... = opt(g \<inter> q)"
  proof -
    have "{\<sigma>. (\<sigma>,\<sigma>) \<in> q} = {\<sigma>. (\<sigma>,\<sigma>) \<in> (g \<inter> q)}"
      using refl unfolding refl_on_def by auto
    then show ?thesis unfolding opt_def by (simp add: sup_commute)
  qed
  finally show ?thesis .
qed

abbreviation P' :: "'b set \<Rightarrow> 'b rel" where
"P' p \<equiv> {(k, k'). k \<in> p \<longrightarrow> k' \<in> p}"

definition
guar_inv :: "('state set) \<Rightarrow> 'a" where
"guar_inv p = (guar (P' p))"

abbreviation guar\<^sub>\<pi> :: "('state \<times> 'state) set \<Rightarrow>'a::refinement_lattice" where
"guar\<^sub>\<pi> p \<equiv> guar p"

abbreviation guar\<^sub>\<epsilon> :: "('state \<times> 'state) set \<Rightarrow>'a::refinement_lattice" where
"guar\<^sub>\<epsilon> p \<equiv> demand p"

definition guar\<^sub>\<alpha> :: "('state \<times> 'state) set \<Rightarrow>'a::refinement_lattice" where
"guar\<^sub>\<alpha> p \<equiv> \<alpha>(p)\<^sup>\<omega>"

lemma guar\<^sub>\<epsilon>_def_2: "guar\<^sub>\<epsilon> p = (restrict p)\<^sup>\<omega>"
  by simp

lemma guar_intro_guar_pgm: "c \<ge> guar\<^sub>\<pi> r \<iinter> c"
  using guar_introduce by blast

lemma guar_intro_guar_env: "c \<ge> guar\<^sub>\<epsilon> r \<iinter> c"
  by (metis atomic_iter_intro guar\<^sub>\<epsilon>_def_2 restrict_atomic)

lemma guar_intro_guar_atomic: "c \<ge> guar\<^sub>\<alpha> r \<iinter> c"
proof -
  have "c \<ge> \<alpha>(r)\<^sup>\<omega> \<iinter> c"
    by (metis atomic_general_atomic atomic_iter_intro)
  then show ?thesis
    using guar\<^sub>\<alpha>_def by auto
qed  

lemma guar_rely_refine_guar_pgm:
  assumes "r\<^sub>1 \<supseteq> r\<^sub>2"
  shows "guar\<^sub>\<pi> r\<^sub>1 \<ge> guar\<^sub>\<pi> r\<^sub>2"
proof -
  show ?thesis
    using assms iter_mono pgm_restrict_strengthen by auto
qed

lemma guar_rely_refine_guar_env:
  assumes "r\<^sub>1 \<supseteq> r\<^sub>2"
  shows "guar\<^sub>\<epsilon> r\<^sub>1 \<ge> guar\<^sub>\<epsilon> r\<^sub>2"
proof -
  show ?thesis
    using assms guar\<^sub>\<epsilon>_def_2 restrict_iter_strengthen by auto
qed

lemma guar_rely_refine_guar_atomic:
  assumes "r\<^sub>1 \<supseteq> r\<^sub>2"
  shows "guar\<^sub>\<alpha> r\<^sub>1 \<ge> guar\<^sub>\<alpha> r\<^sub>2"
proof -
  show ?thesis
    by (simp add: assms general_atomic.hom_mono guar\<^sub>\<alpha>_def iter_mono)
qed

lemma guar_rely_refine_rely:
  assumes "r\<^sub>1 \<supseteq> r\<^sub>2"
  shows "rely r\<^sub>2 \<ge> rely r\<^sub>1"
proof -
  show ?thesis
    using assms rely_weaken by auto
qed

lemma introduce_guar_pgm: "c \<ge> guar\<^sub>\<pi> p \<iinter> c" 
  using guar_introduce by auto

lemma introduce_guar_env: "c \<ge> guar\<^sub>\<epsilon> p \<iinter> c"
  by (metis conj.sync_mono_right conj_chaos guar\<^sub>\<epsilon>_def_2 local.conj_commute restrict_iter_nonaborting)

lemma introduce_guar_atomic: "c \<ge> guar\<^sub>\<alpha> p \<iinter> c"
  by (metis atomic_general_atomic atomic_iter_intro guar\<^sub>\<alpha>_def)

lemma guar_rely_merge_guar_pgm: "guar\<^sub>\<pi> r\<^sub>1 \<iinter> guar\<^sub>\<pi> r\<^sub>2 = guar\<^sub>\<pi> (r\<^sub>1 \<inter> r\<^sub>2)"
  using guar_merge by auto

lemma guar_rely_merge_guar_env: "guar\<^sub>\<epsilon> r\<^sub>1 \<iinter> guar\<^sub>\<epsilon> r\<^sub>2 = guar\<^sub>\<epsilon> (r\<^sub>1 \<inter> r\<^sub>2)"
  using guar\<^sub>\<epsilon>_def_2 restrict_iter_conj_to_inf by auto

lemma guar_rely_merge_guar_atomic: "guar\<^sub>\<alpha> r\<^sub>1 \<iinter> guar\<^sub>\<alpha> r\<^sub>2 = guar\<^sub>\<alpha> (r\<^sub>1 \<inter> r\<^sub>2)"
proof -
  have "guar\<^sub>\<alpha> r\<^sub>1 \<iinter> guar\<^sub>\<alpha> r\<^sub>2 = \<alpha>(r\<^sub>1)\<^sup>\<omega> \<iinter> \<alpha>(r\<^sub>2)\<^sup>\<omega>"
    by (simp add: guar\<^sub>\<alpha>_def)
  also have "... = (\<alpha>(r\<^sub>1) \<iinter> \<alpha>(r\<^sub>2))\<^sup>\<omega>"
    by (metis conj.atomic_iter_sync_iter atomic_general_atomic)
  also have "... = \<alpha>(r\<^sub>1 \<inter> r\<^sub>2)\<^sup>\<omega>"
    by (simp add: general_atomic_def pgmenv_conj_pgmenv)
  finally show ?thesis
    by (simp add: guar\<^sub>\<alpha>_def)
qed

lemma guar_rely_merge_rely: "rely r\<^sub>1 \<iinter> rely r\<^sub>2 = rely (r\<^sub>1 \<inter> r\<^sub>2)"
  using rely_conj_rely by auto

lemma guar_atomic_merge_parallel: "guar\<^sub>\<alpha> r\<^sub>1 \<parallel> guar\<^sub>\<alpha> r\<^sub>2 = guar\<^sub>\<alpha> (r\<^sub>1 \<inter> r\<^sub>2)"
proof -
  have atomic_merge: "\<alpha>(r\<^sub>1) \<parallel> \<alpha>(r\<^sub>2) = \<alpha>(r\<^sub>1 \<inter> r\<^sub>2)"
      by (simp add: pgm_env_parallel general_atomic_def)

  have "guar\<^sub>\<alpha> r\<^sub>1 \<parallel> guar\<^sub>\<alpha> r\<^sub>2 = \<alpha>(r\<^sub>1)\<^sup>\<omega> \<parallel> \<alpha>(r\<^sub>2)\<^sup>\<omega>"
    by (simp add: guar\<^sub>\<alpha>_def)
  also have "... = (\<alpha>(r\<^sub>1) \<parallel> \<alpha>(r\<^sub>2))\<^sup>\<omega>"
    by (metis par.atomic_iter_sync_iter atomic_general_atomic)
  also have "... = \<alpha>(r\<^sub>1 \<inter> r\<^sub>2)\<^sup>\<omega>"
    by (simp add: atomic_merge)
  finally show ?thesis
    by (simp add: guar\<^sub>\<alpha>_def)
qed

lemma guar_atomic_merge_inf: "guar\<^sub>\<alpha> r\<^sub>1 \<sqinter> guar\<^sub>\<alpha> r\<^sub>2 = guar\<^sub>\<alpha> (r\<^sub>1 \<inter> r\<^sub>2)"
proof -
  have "guar\<^sub>\<alpha> r\<^sub>1 \<sqinter> guar\<^sub>\<alpha> r\<^sub>2 = \<alpha>(r\<^sub>1)\<^sup>\<omega> \<sqinter> \<alpha>(r\<^sub>2)\<^sup>\<omega>"
    by (simp add: guar\<^sub>\<alpha>_def)
  also have "... = (\<alpha>(r\<^sub>1) \<sqinter> \<alpha>(r\<^sub>2))\<^sup>\<omega>"
    by (metis inf.atomic_iter_sync_iter atomic_general_atomic)
  finally show ?thesis
    by (simp add: guar\<^sub>\<alpha>_def)
qed

lemma psuedo_atomic_fixed_point_guar_pgm: "guar\<^sub>\<pi> g = (atomic(g, \<top>) \<squnion> atomic \<bottom> ; \<top>) ; guar\<^sub>\<pi> g \<squnion> nil"
proof -
  have "guar\<^sub>\<pi> g = atomic(g, \<top>)\<^sup>\<omega>"
    by (simp add: Env_def atomic_def)
  also have "... = (atomic(g, \<top>) \<squnion> atomic \<bottom> ; \<top>) ; atomic(g, \<top>)\<^sup>\<omega> \<squnion> nil"
    by (metis par.pseudo_atomic_fixed_points_iter)
  finally show ?thesis
    by (simp add: Env_def atomic_def)
qed

lemma psuedo_atomic_fixed_point_guar_env: "guar\<^sub>\<epsilon> g = (atomic(\<top>, g) \<squnion> atomic \<bottom> ; \<top>) ; guar\<^sub>\<epsilon> g \<squnion> nil"
proof -
  have "guar\<^sub>\<epsilon> g = atomic(\<top>, g)\<^sup>\<omega>"
    by (simp add: guar\<^sub>\<epsilon>_def_2 Pgm_def atomic_def sup_commute)
  also have "... = (atomic(\<top>, g) \<squnion> atomic \<bottom> ; \<top>) ; atomic(\<top>, g)\<^sup>\<omega> \<squnion> nil"
    by (metis par.pseudo_atomic_fixed_points_iter)
  finally show ?thesis
    by (simp add: guar\<^sub>\<epsilon>_def_2 Pgm_def atomic_def sup_commute)
qed

lemma psuedo_atomic_fixed_point_guar_atomic: "guar\<^sub>\<alpha> g = (atomic(g, g) \<squnion> atomic \<bottom> ; \<top>) ; guar\<^sub>\<alpha> g \<squnion> nil"
proof -
  have "guar\<^sub>\<alpha> g = atomic(g, g)\<^sup>\<omega>"
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def)
  also have "... = (atomic(g, g) \<squnion> atomic \<bottom> ; \<top>) ; atomic(g, g)\<^sup>\<omega> \<squnion> nil"
    by (metis par.pseudo_atomic_fixed_points_iter)
  finally show ?thesis
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def)
qed

lemma psuedo_atomic_fixed_point_rely: "rely r = (atomic(\<top>, r) \<squnion> (atomic.negate(\<epsilon>(r)) \<sqinter> \<E>) ; \<top>) ; rely r \<squnion> nil"
proof -
  have "rely r = (atomic(\<top>, r) \<squnion> (atomic.negate(\<epsilon>(r)) \<sqinter> \<E>);\<top>)\<^sup>\<omega>"
    by (simp add: Pgm_def atomic_def sup_commute)
  also have "... = (atomic(\<top>, r) \<squnion> (atomic.negate(\<epsilon>(r)) \<sqinter> \<E>) ; \<top>) ; rely r \<squnion> nil"
    by (metis calculation negate_env_sup_Env_atomic par.pseudo_atomic_fixed_points_pseudo_iter)
  finally show ?thesis .
qed

lemma pseudo_atomic_distrib_test_par_guar_pgm: "guar\<^sub>\<pi> g \<parallel> \<tau> p = \<tau> p"
  using par.atomic_distributing_test psuedo_atomic_fixed_point_guar_pgm by blast

lemma pseudo_atomic_distrib_test_conj_guar_pgm: "guar\<^sub>\<pi> g \<iinter> \<tau> p = \<tau> p"
  using conj.atomic_distributing_test psuedo_atomic_fixed_point_guar_pgm by blast

lemma pseudo_atomic_distrib_test_inf_guar_pgm: "guar\<^sub>\<pi> g \<sqinter> \<tau> p = \<tau> p"
  using inf.atomic_distributing_test psuedo_atomic_fixed_point_guar_pgm by blast

lemma pseudo_atomic_distrib_test_par_guar_env: "guar\<^sub>\<epsilon> g \<parallel> \<tau> p = \<tau> p"
  by (meson par.atomic_distributing_test psuedo_atomic_fixed_point_guar_env)

lemma pseudo_atomic_distrib_test_conj_guar_env: "guar\<^sub>\<epsilon> g \<iinter> \<tau> p = \<tau> p"
  by (meson conj.atomic_distributing_test psuedo_atomic_fixed_point_guar_env)

lemma pseudo_atomic_distrib_test_inf_guar_env: "guar\<^sub>\<epsilon> g \<sqinter> \<tau> p = \<tau> p"
  by (meson inf.atomic_distributing_test psuedo_atomic_fixed_point_guar_env)

lemma pseudo_atomic_distrib_test_par_guar_atomic: "guar\<^sub>\<alpha> g \<parallel> \<tau> p = \<tau> p"
  using par.atomic_distributing_test psuedo_atomic_fixed_point_guar_atomic by blast

lemma pseudo_atomic_distrib_test_conj_guar_atomic: "guar\<^sub>\<alpha> g \<iinter> \<tau> p = \<tau> p"
  using conj.atomic_distributing_test psuedo_atomic_fixed_point_guar_atomic by blast

lemma pseudo_atomic_distrib_test_inf_guar_atomic: "guar\<^sub>\<alpha> g \<sqinter> \<tau> p = \<tau> p"
  using inf.atomic_distributing_test psuedo_atomic_fixed_point_guar_atomic by blast

lemma pseudo_atomic_distrib_test_par_rely: "rely r \<parallel> \<tau> p = \<tau> p"
  by (metis Pgm_def env_assump_def5 env_atomic env_or_Pgm_atomic iter_unfold par.atomic_distributing_test rely_def sup_commute)

lemma pseudo_atomic_distrib_test_conj_rely: "rely r \<iinter> \<tau> p = \<tau> p"
  by (metis Pgm_def env_assump_def5 env_atomic env_or_Pgm_atomic iter_unfold conj.atomic_distributing_test rely_def sup_commute)

lemma pseudo_atomic_distrib_test_inf_rely: "rely r \<sqinter> \<tau> p = \<tau> p"
  by (metis Pgm_def env_assump_def5 env_atomic env_or_Pgm_atomic iter_unfold inf.atomic_distributing_test rely_def sup_commute)

lemma pseudo_atomic_distrib_Nondet_par_guar_pgm: "guar\<^sub>\<pi> g \<parallel> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<pi> g \<parallel> d)"
  by (metis SUP_empty Sup_empty par.sync_Nondet_distrib pseudo_atomic_distrib_test_par_guar_pgm test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_conj_guar_pgm: "guar\<^sub>\<pi> g \<iinter> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<pi> g \<iinter> d)"
  by (metis SUP_empty Sup_empty conj.sync_Nondet_distrib pseudo_atomic_distrib_test_conj_guar_pgm test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_inf_guar_pgm: "guar\<^sub>\<pi> g \<sqinter> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<pi> g \<sqinter> d)"
  by (metis SUP_empty Sup_empty inf.sync_Nondet_distrib pseudo_atomic_distrib_test_inf_guar_pgm test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_par_guar_env: "guar\<^sub>\<epsilon> g \<parallel> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<epsilon> g \<parallel> d)"
  by (metis SUP_empty Sup_empty par.sync_Nondet_distrib pseudo_atomic_distrib_test_par_guar_env test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_conj_guar_env: "guar\<^sub>\<epsilon> g \<iinter> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<epsilon> g \<iinter> d)"
  by (metis SUP_empty Sup_empty conj.sync_Nondet_distrib pseudo_atomic_distrib_test_conj_guar_env test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_inf_guar_env: "guar\<^sub>\<epsilon> g \<sqinter> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<epsilon> g \<sqinter> d)"
  by (metis SUP_empty Sup_empty inf.sync_Nondet_distrib pseudo_atomic_distrib_test_inf_guar_env test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_par_guar_atomic: "guar\<^sub>\<alpha> g \<parallel> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<alpha> g \<parallel> d)"
  by (metis SUP_empty Sup_empty par.sync_Nondet_distrib pseudo_atomic_distrib_test_par_guar_atomic test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_conj_guar_atomic: "guar\<^sub>\<alpha> g \<iinter> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<alpha> g \<iinter> d)"
  by (metis SUP_empty Sup_empty conj.sync_Nondet_distrib pseudo_atomic_distrib_test_conj_guar_atomic test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_inf_guar_atomic: "guar\<^sub>\<alpha> g \<sqinter> (\<Squnion>D) = (\<Squnion>d \<in> D. guar\<^sub>\<alpha> g \<sqinter> d)"
  by (metis SUP_empty Sup_empty inf.sync_Nondet_distrib pseudo_atomic_distrib_test_inf_guar_atomic test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_par_rely: "rely r \<parallel> (\<Squnion>D) = (\<Squnion>d \<in> D. rely r \<parallel> d)"
  by (metis SUP_empty Sup_empty par.sync_Nondet_distrib pseudo_atomic_distrib_test_par_rely test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_conj_rely: "rely r \<iinter> (\<Squnion>D) = (\<Squnion>d \<in> D. rely r \<iinter> d)"
  by (metis SUP_empty Sup_empty conj.sync_Nondet_distrib pseudo_atomic_distrib_test_conj_rely test.hom_bot) 

lemma pseudo_atomic_distrib_Nondet_inf_rely: "rely r \<sqinter> (\<Squnion>D) = (\<Squnion>d \<in> D. rely r \<sqinter> d)"
  by (metis SUP_empty Sup_empty inf.sync_Nondet_distrib pseudo_atomic_distrib_test_inf_rely test.hom_bot) 

lemma pseudo_atomic_distrib_assert_par_guar_pgm: "guar\<^sub>\<pi> g \<parallel> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis assert_seq_test par.assert_distrib pseudo_atomic_distrib_test_par_guar_pgm)

lemma pseudo_atomic_distrib_assert_conj_guar_pgm: "guar\<^sub>\<pi> g \<iinter> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis assert_seq_test conj.assert_distrib pseudo_atomic_distrib_test_conj_guar_pgm)

lemma pseudo_atomic_distrib_assert_par_guar_env: "guar\<^sub>\<epsilon> g \<parallel> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis assert_seq_test par.assert_distrib pseudo_atomic_distrib_test_par_guar_env)

lemma pseudo_atomic_distrib_assert_conj_guar_env: "guar\<^sub>\<epsilon> g \<iinter> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis assert_seq_test conj.assert_distrib pseudo_atomic_distrib_test_conj_guar_env)

lemma pseudo_atomic_distrib_assert_par_guar_atomic: "guar\<^sub>\<alpha> g \<parallel> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis assert_seq_test par.assert_distrib pseudo_atomic_distrib_test_par_guar_atomic)

lemma pseudo_atomic_distrib_assert_conj_guar_atomic: "guar\<^sub>\<alpha> g \<iinter> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis assert_seq_test conj.assert_distrib pseudo_atomic_distrib_test_conj_guar_atomic)

lemma pseudo_atomic_distrib_assert_par_rely: "rely r \<parallel> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis assert_seq_test par.assert_distrib pseudo_atomic_distrib_test_par_rely)

lemma pseudo_atomic_distrib_assert_conj_rely: "rely r \<iinter> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis assert_seq_test conj.assert_distrib pseudo_atomic_distrib_test_conj_rely)

lemma distrib_seq_par_guar_pgm: "guar\<^sub>\<pi> g \<parallel> (c ; d) = (guar\<^sub>\<pi> g \<parallel> c) ; (guar\<^sub>\<pi> g \<parallel> d)"
  by (metis par.atomic_iter_distrib_seq psuedo_atomic_fixed_point_guar_pgm)

lemma distrib_seq_conj_guar_pgm: "guar\<^sub>\<pi> g \<iinter> (c ; d) = (guar\<^sub>\<pi> g \<iinter> c) ; (guar\<^sub>\<pi> g \<iinter> d)"
  by (metis conj.atomic_iter_distrib_seq psuedo_atomic_fixed_point_guar_pgm)

lemma distrib_seq_par_guar_env: "guar\<^sub>\<epsilon> g \<parallel> (c ; d) = (guar\<^sub>\<epsilon> g \<parallel> c) ; (guar\<^sub>\<epsilon> g \<parallel> d)"
  by (metis par.atomic_iter_distrib_seq psuedo_atomic_fixed_point_guar_env)

lemma distrib_seq_conj_guar_env: "guar\<^sub>\<epsilon> g \<iinter> (c ; d) = (guar\<^sub>\<epsilon> g \<iinter> c) ; (guar\<^sub>\<epsilon> g \<iinter> d)"
  by (metis conj.atomic_iter_distrib_seq psuedo_atomic_fixed_point_guar_env)

lemma distrib_seq_par_guar_atomic: "guar\<^sub>\<alpha> g \<parallel> (c ; d) = (guar\<^sub>\<alpha> g \<parallel> c) ; (guar\<^sub>\<alpha> g \<parallel> d)"
  by (metis par.atomic_iter_distrib_seq psuedo_atomic_fixed_point_guar_atomic)

lemma distrib_seq_conj_guar_atomic: "guar\<^sub>\<alpha> g \<iinter> (c ; d) = (guar\<^sub>\<alpha> g \<iinter> c) ; (guar\<^sub>\<alpha> g \<iinter> d)"
  by (metis conj.atomic_iter_distrib_seq psuedo_atomic_fixed_point_guar_atomic)

lemma distrib_seq_par_rely: "rely r \<parallel> (c ; d) = (rely r \<parallel> c) ; (rely r \<parallel> d)"
  by (metis psuedo_atomic_fixed_point_rely par.atomic_iter_distrib_seq negate_env_sup_Env_atomic)

lemma distrib_seq_conj_rely: "rely r \<iinter> (c ; d) = (rely r \<iinter> c) ; (rely r \<iinter> d)"
  by (metis psuedo_atomic_fixed_point_rely conj.atomic_iter_distrib_seq negate_env_sup_Env_atomic)

lemma pseudo_distrib_finite_iter_par_guar_pgm: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "guar\<^sub>\<pi> g \<parallel> c\<^sup>\<star> = (guar\<^sub>\<pi> g \<parallel> c)\<^sup>\<star>"
  by (metis distrib_seq_par_guar_pgm par.distrib_finite_iter pseudo_atomic_distrib_test_par_guar_pgm test_top)

lemma pseudo_distrib_finite_iter_conj_guar_pgm: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "guar\<^sub>\<pi> g \<iinter> c\<^sup>\<star> = (guar\<^sub>\<pi> g \<iinter> c)\<^sup>\<star>"
  by (metis distrib_seq_conj_guar_pgm conj.distrib_finite_iter pseudo_atomic_distrib_test_conj_guar_pgm test_top)

lemma pseudo_distrib_finite_iter_par_guar_env: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "guar\<^sub>\<epsilon> g \<parallel> c\<^sup>\<star> = (guar\<^sub>\<epsilon> g \<parallel> c)\<^sup>\<star>"
  by (metis distrib_seq_par_guar_env par.distrib_finite_iter pseudo_atomic_distrib_test_par_guar_env test_top)

lemma pseudo_distrib_finite_iter_conj_guar_env: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "guar\<^sub>\<epsilon> g \<iinter> c\<^sup>\<star> = (guar\<^sub>\<epsilon> g \<iinter> c)\<^sup>\<star>"
  by (metis distrib_seq_conj_guar_env conj.distrib_finite_iter pseudo_atomic_distrib_test_conj_guar_env test_top)

lemma pseudo_distrib_finite_iter_par_guar_atomic: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "guar\<^sub>\<alpha> g \<parallel> c\<^sup>\<star> = (guar\<^sub>\<alpha> g \<parallel> c)\<^sup>\<star>"
  by (metis distrib_seq_par_guar_atomic par.distrib_finite_iter pseudo_atomic_distrib_test_par_guar_atomic test_top)

lemma pseudo_distrib_finite_iter_conj_guar_atomic: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "guar\<^sub>\<alpha> g \<iinter> c\<^sup>\<star> = (guar\<^sub>\<alpha> g \<iinter> c)\<^sup>\<star>"
  by (metis distrib_seq_conj_guar_atomic conj.distrib_finite_iter pseudo_atomic_distrib_test_conj_guar_atomic test_top)

lemma pseudo_distrib_finite_iter_par_rely: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "rely r \<parallel> c\<^sup>\<star> = (rely r \<parallel> c)\<^sup>\<star>"
  by (metis distrib_seq_par_rely par.distrib_finite_iter pseudo_atomic_distrib_test_par_rely test_top)

lemma pseudo_distrib_finite_iter_conj_rely: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "rely r \<iinter> c\<^sup>\<star> = (rely r \<iinter> c)\<^sup>\<star>"
  by (metis distrib_seq_conj_rely conj.distrib_finite_iter pseudo_atomic_distrib_test_conj_rely test_top)

lemma distrib_iter_par_guar_pgm: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "guar\<^sub>\<pi> g \<parallel> c\<^sup>\<omega> = (guar\<^sub>\<pi> g \<parallel> c)\<^sup>\<omega>"
proof -
  have "guar\<^sub>\<pi> g = (atomic(g, \<top>))\<^sup>\<omega>"
    by (simp add: Env_def atomic_def)
  also have a1: "... = (atomic(g, \<top>) \<squnion> atomic \<bottom> ; \<top>)\<^sup>\<omega>"
    by simp
  show ?thesis
    by (metis assms par.atomic_iter_distrib_iter a1 calculation)
qed

lemma distrib_iter_conj_guar_pgm: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "guar\<^sub>\<pi> g \<iinter> c\<^sup>\<omega> = (guar\<^sub>\<pi> g \<iinter> c)\<^sup>\<omega>"
proof -
  have "guar\<^sub>\<pi> g = (atomic(g, \<top>))\<^sup>\<omega>"
    by (simp add: Env_def atomic_def)
  also have a1: "... = (atomic(g, \<top>) \<squnion> atomic \<bottom> ; \<top>)\<^sup>\<omega>"
    by simp
  show ?thesis
    by (metis assms conj.atomic_iter_distrib_iter a1 calculation)
qed

lemma distrib_iter_par_guar_env: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "guar\<^sub>\<epsilon> g \<parallel> c\<^sup>\<omega> = (guar\<^sub>\<epsilon> g \<parallel> c)\<^sup>\<omega>"
proof -
  have "guar\<^sub>\<epsilon> g = (atomic(\<top>, g))\<^sup>\<omega>"
    by (simp add: guar\<^sub>\<epsilon>_def_2 Pgm_def atomic_def sup_commute)
  also have a1: "... = (atomic(\<top>, g) \<squnion> atomic \<bottom> ; \<top>)\<^sup>\<omega>"
    by simp
  show ?thesis
    by (metis assms par.atomic_iter_distrib_iter a1 calculation)
qed

lemma distrib_iter_conj_guar_env: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "guar\<^sub>\<epsilon> g \<iinter> c\<^sup>\<omega> = (guar\<^sub>\<epsilon> g \<iinter> c)\<^sup>\<omega>"
proof -
  have "guar\<^sub>\<epsilon> g = (atomic(\<top>, g))\<^sup>\<omega>"
    by (simp add: guar\<^sub>\<epsilon>_def_2 Pgm_def atomic_def sup_commute)
  also have a1: "... = (atomic(\<top>, g) \<squnion> atomic \<bottom> ; \<top>)\<^sup>\<omega>"
    by simp
  show ?thesis
    by (metis assms conj.atomic_iter_distrib_iter a1 calculation)
qed

lemma distrib_iter_par_guar_atomic: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "guar\<^sub>\<alpha> g \<parallel> c\<^sup>\<omega> = (guar\<^sub>\<alpha> g \<parallel> c)\<^sup>\<omega>"
proof -
  have "guar\<^sub>\<alpha> g = (atomic(g, g))\<^sup>\<omega>"
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def)
  also have a1: "... = (atomic(g, g) \<squnion> atomic \<bottom> ; \<top>)\<^sup>\<omega>"
    by simp
  show ?thesis
    by (metis assms par.atomic_iter_distrib_iter a1 calculation)
qed

lemma distrib_iter_conj_guar_atomic: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "guar\<^sub>\<alpha> g \<iinter> c\<^sup>\<omega> = (guar\<^sub>\<alpha> g \<iinter> c)\<^sup>\<omega>"
proof -
  have "guar\<^sub>\<alpha> g = (atomic(g, g))\<^sup>\<omega>"
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def)
  also have a1: "... = (atomic(g, g) \<squnion> atomic \<bottom> ; \<top>)\<^sup>\<omega>"
    by simp
  show ?thesis
    by (metis assms conj.atomic_iter_distrib_iter a1 calculation)
qed

lemma distrib_iter_par_rely: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "rely r \<parallel> c\<^sup>\<omega> = (rely r \<parallel> c)\<^sup>\<omega>"
proof -
  have a1: "rely r = (atomic(\<top>, r) \<squnion> (atomic.negate(\<epsilon>(r)) \<sqinter> \<E>);\<top>)\<^sup>\<omega>"
    by (simp add: Pgm_def atomic_def sup_commute) 
  show ?thesis
    by (metis assms par.atomic_iter_distrib_iter a1 negate_env_sup_Env_atomic negate_env_sup_Env_atomic)
qed

lemma distrib_iter_conj_rely: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "rely r \<iinter> c\<^sup>\<omega> = (rely r \<iinter> c)\<^sup>\<omega>"
proof -
  have a1: "rely r = (atomic(\<top>, r) \<squnion> (atomic.negate(\<epsilon>(r)) \<sqinter> \<E>);\<top>)\<^sup>\<omega>"
    by (simp add: Pgm_def atomic_def sup_commute) 
  show ?thesis
    by (metis assms conj.atomic_iter_distrib_iter a1 negate_env_sup_Env_atomic negate_env_sup_Env_atomic)
qed

lemma par_distrib_guar_pgm: "guar\<^sub>\<pi> g \<iinter> (c \<parallel> d) = (guar\<^sub>\<pi> g \<iinter> c) \<parallel> (guar\<^sub>\<pi> g \<iinter> d)"
proof -
  have step_par_idem: "(\<pi>(g) \<squnion> \<E>) = (\<pi>(g) \<squnion> \<E>) \<parallel> (\<pi>(g) \<squnion> \<E>)"
    by (simp add: Env_def pgmenv_par_pgmenv)
  have step_other_form: "(\<pi>(g) \<squnion> \<E>) = atomic(g, \<top>)"
    by (simp add: Env_def atomic_def)
  have guar_expanded: "guar\<^sub>\<pi> g = (\<pi>(g) \<squnion> \<E>)\<^sup>\<omega>"
    by simp
  show ?thesis
    by (metis step_par_idem guar_expanded step_other_form par_distrib_if_idempotent)
qed

lemma par_distrib_guar_atomic: "guar\<^sub>\<alpha> g \<iinter> (c \<parallel> d) = (guar\<^sub>\<alpha> g \<iinter> c) \<parallel> (guar\<^sub>\<alpha> g \<iinter> d)"
proof -
  have step_par_idem: "(\<pi>(g) \<squnion> \<epsilon>(g)) = (\<pi>(g) \<squnion> \<epsilon>(g)) \<parallel> (\<pi>(g) \<squnion> \<epsilon>(g))"
    by (simp add: par_atomic_idempotent)
  have step_other_form: "(\<pi>(g) \<squnion> \<epsilon>(g)) = atomic(g, g)"
    by (simp add: Env_def atomic_def)
  have guar_expanded: "guar\<^sub>\<alpha> g = (\<pi>(g) \<squnion> \<epsilon>(g))\<^sup>\<omega>"
    by (simp add: general_atomic_def guar\<^sub>\<alpha>_def)
  show ?thesis
    by (metis step_par_idem guar_expanded step_other_form par_distrib_if_idempotent)
qed

lemma evolve_split: "guar\<^sub>\<alpha> r = guar\<^sub>\<pi> r \<iinter> guar\<^sub>\<epsilon> r"
proof -
  have "guar\<^sub>\<alpha> r = (\<pi> r \<squnion> \<epsilon> r)\<^sup>\<omega>"
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def general_atomic_def)
  also have "... = (atomic(r, \<top>) \<iinter> atomic(\<top>, r))\<^sup>\<omega>"
    by (simp add: pgmenv_conj_pgmenv atomic_def)
  also have "... = atomic(r, \<top>)\<^sup>\<omega> \<iinter> atomic(\<top>, r)\<^sup>\<omega>"
    by (metis conj.atomic_iter_sync_iter)
  also have "... = (\<pi> r \<squnion> \<E>)\<^sup>\<omega> \<iinter> (Pgm \<squnion> \<epsilon> r)\<^sup>\<omega>"
    by (simp add: atomic_def Env_def Pgm_def)
  also have "... = guar\<^sub>\<pi> r \<iinter> guar\<^sub>\<epsilon> r"
    by (simp add: guar\<^sub>\<epsilon>_def_2 sup_commute)
  finally show ?thesis .
qed

lemma evolve_guar: "guar\<^sub>\<epsilon> r \<iinter> guar\<^sub>\<pi> (g \<inter> r) = guar\<^sub>\<alpha> r \<iinter> guar\<^sub>\<pi> g"
  using evolve_split guar_merge local.conj_assoc local.conj_commute by fastforce

lemma evolve_split_par: "guar\<^sub>\<alpha> r \<iinter> (c \<parallel> d) = guar\<^sub>\<epsilon> r \<iinter>((guar\<^sub>\<pi> r \<iinter> c) \<parallel> (guar\<^sub>\<pi> r \<iinter> d))"
  by (metis conj.comm.left_commute par_distrib_guar_pgm evolve_split local.conj_commute)

lemma guar_distrib_step_pgm_helper: "guar\<^sub>\<pi> r = (atomic(r, \<top>) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega>"
proof -
  have "guar\<^sub>\<pi> r = (\<pi>(r) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>"
    by (simp add: Env_def)
  also have "... = atomic(r, \<top>)\<^sup>\<omega>"
    by (simp add: atomic_def)
  finally show ?thesis
    by simp
qed

lemma guar_distrib_step_pgm_pgm: "guar\<^sub>\<pi> r \<iinter> \<pi>(q) = \<pi>(r \<inter> q)"
proof -
  have a1: "\<pi>(q) = atomic(q, \<bottom>)"
    by (simp add: atomic_def)
  have "guar\<^sub>\<pi> r \<iinter> \<pi>(q) = (atomic(r, \<top>) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(q, \<bottom>)"
    using a1 guar_distrib_step_pgm_helper by auto
  also have "... = (atomic(r, \<top>) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(q, \<bottom>)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(r, \<top>) \<iinter> atomic(q, \<bottom>)"
    by simp
  also have "... = atomic(r \<inter> q, \<top> \<inter> \<bottom>)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    using guar_conj_pgm by auto
qed

lemma guar_distrib_step_pgm_env: "guar\<^sub>\<pi> r \<iinter> \<epsilon>(q) = \<epsilon>(q)"
proof -
  have a1: "\<epsilon>(q) = atomic(\<bottom>, q)"
    by (simp add: atomic_def)
  have "guar\<^sub>\<pi> r \<iinter> \<epsilon>(q) = (atomic(r, \<top>) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(\<bottom>, q)"
    using a1 guar_distrib_step_pgm_helper by auto
  also have "... = (atomic(r, \<top>) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(\<bottom>, q)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(r, \<top>) \<iinter> atomic(\<bottom>, q)"
    by simp
  also have "... = atomic(r \<inter> \<bottom>, \<top> \<inter> q)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: atomic_def)
qed

lemma guar_distrib_step_pgm_atomic: "guar\<^sub>\<pi> r \<iinter> \<alpha>(q) = \<pi>(r \<inter> q) \<squnion> \<epsilon>(q)"
proof -
  have "guar\<^sub>\<pi> r \<iinter> \<alpha>(q) = (atomic(r, \<top>) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(q, q)"
    using atomic_general_atomic guar_distrib_step_pgm_helper by auto
  also have "... = (atomic(r, \<top>) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(q, q)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(r, \<top>) \<iinter> atomic(q, q)"
    by simp
  also have "... = atomic(r \<inter> q, \<top> \<inter> q)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    using conj.sync_nondet_distrib general_atomic_def guar_conj_pgm guar_distrib_step_pgm_env by presburger
qed

lemma guar_distrib_step_env_helper: "guar\<^sub>\<epsilon> r = (atomic(\<top>, r) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega>"
proof -
  have "guar\<^sub>\<epsilon> r = (\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>"
    by (simp add: Pgm_def guar\<^sub>\<epsilon>_def_2 inf_sup_aci(5))
  also have "... = atomic(\<top>, r)\<^sup>\<omega>"
    by (simp add: atomic_def)
  finally show ?thesis
    by simp
qed

lemma guar_distrib_step_env_pgm: "guar\<^sub>\<epsilon> r \<iinter> \<pi>(q) = \<pi>(q)"
proof -
  have a1: "\<pi>(q) = atomic(q, \<bottom>)"
    by (simp add: atomic_def)
  have "guar\<^sub>\<epsilon> r \<iinter> \<pi>(q) = (atomic(\<top>, r) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(q, \<bottom>)"
    using a1 guar_distrib_step_env_helper by auto
  also have "... = (atomic(\<top>, r) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(q, \<bottom>)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(\<top>, r) \<iinter> atomic(q, \<bottom>)"
    by simp
  also have "... = atomic(\<top> \<inter> q, r \<inter> \<bottom>)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: a1)
qed

lemma guar_distrib_step_env_env: "guar\<^sub>\<epsilon> r \<iinter> \<epsilon>(q) = \<epsilon>(r \<inter> q)"
proof -
  have a1: "\<epsilon>(q) = atomic(\<bottom>, q)"
    by (simp add: atomic_def)
  have "guar\<^sub>\<epsilon> r \<iinter> \<epsilon>(q) = (atomic(\<top>, r) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(\<bottom>, q)"
    using a1 guar_distrib_step_env_helper by auto
  also have "... = (atomic(\<top>, r) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(\<bottom>, q)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(\<top>, r) \<iinter> atomic(\<bottom>, q)"
    by simp
  also have "... = atomic(\<top> \<inter> \<bottom>, r \<inter> q)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: atomic_def)
qed

lemma guar_distrib_step_env_atomic: "guar\<^sub>\<epsilon> r \<iinter> \<alpha>(q) = \<pi>(q) \<squnion> \<epsilon>(r \<inter> q)"
proof -
  have "guar\<^sub>\<epsilon> r \<iinter> \<alpha>(q) = (atomic(\<top>, r) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(q, q)"
    using atomic_general_atomic guar_distrib_step_env_helper by auto
  also have "... = (atomic(\<top>, r) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(q, q)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(\<top>, r) \<iinter> atomic(q, q)"
    by simp
  also have "... = atomic(\<top> \<inter> q, r \<inter> q)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (metis conj.nondet_sync_distrib general_atomic_def guar_distrib_step_env_env guar_distrib_step_env_pgm local.conj_commute)
qed

lemma guar_distrib_step_atomic_pgm: "guar\<^sub>\<alpha> r \<iinter> \<pi>(q) = \<pi>(r \<inter> q)"
proof -
  have a1: "\<pi>(q) = atomic(q, \<bottom>)"
    by (simp add: atomic_def)
  have "guar\<^sub>\<alpha> r \<iinter> \<pi>(q) = (atomic(r, r) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(q, \<bottom>)"
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def a1)
  also have "... = (atomic(r, r) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(q, \<bottom>)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(r, r) \<iinter> atomic(q, \<bottom>)"
    by simp
  also have "... = atomic(r \<inter> q, r \<inter> \<bottom>)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: atomic_def)
qed

lemma guar_distrib_step_atomic_env: "guar\<^sub>\<alpha> r \<iinter> \<epsilon>(q) = \<epsilon>(r \<inter> q)"
proof -
  have a1: "\<epsilon>(q) = atomic(\<bottom>, q)"
    by (simp add: atomic_def)
  have "guar\<^sub>\<alpha> r \<iinter> \<epsilon>(q) = (atomic(r, r) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(\<bottom>, q)"
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def a1)
  also have "... = (atomic(r, r) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(\<bottom>, q)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(r, r) \<iinter> atomic(\<bottom>, q)"
    by simp
  also have "... = atomic(r \<inter> \<bottom>, r \<inter> q)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: atomic_def)
qed

lemma guar_distrib_step_atomic_atomic: "guar\<^sub>\<alpha> r \<iinter> \<alpha>(q) = \<alpha>(r \<inter> q)"
proof -
  have "guar\<^sub>\<alpha> r \<iinter> \<alpha>(q) = (atomic(r, r) \<squnion> atomic(\<bottom>) ; \<top>)\<^sup>\<omega> \<iinter> atomic(q, q)"
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def)
  also have "... = (atomic(r, r) \<squnion> atomic(\<bottom>) ; \<top>) \<iinter> atomic(q, q)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(r, r) \<iinter> atomic(q, q)"
    by simp
  also have "... = atomic(r \<inter> q, r \<inter> q)"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: atomic_general_atomic)
qed

lemma rely_distrib_step_helper: "rely r = (atomic(\<top>, r) \<squnion> atomic(\<bottom>, -r) ; \<top>)\<^sup>\<omega>"
proof -
  have a1: "(\<epsilon>(r) \<squnion> Pgm) = atomic(\<top>, r)"
    by (simp add: Pgm_def sup_commute atomic_def)
  have a2: "atomic.negate(\<epsilon>(r)) \<sqinter> \<E> = atomic(\<bottom>, -r)"
    by (simp add: a1 negate_env_sup_Env)
  show ?thesis 
    by (simp add: a1 a2)
qed

lemma rely_distrib_step_pgm: "rely r \<iinter> \<pi>(q) = \<pi>(q)"
proof -
  have a1: "\<pi>(q) = atomic(q, \<bottom>)"
    by (simp add: atomic_def)
  have "rely r \<iinter> \<pi>(q) = (atomic(\<top>, r) \<squnion> atomic(\<bottom>, -r) ; \<top>)\<^sup>\<omega> \<iinter> atomic(q, \<bottom>)"
    by (metis rely_distrib_step_helper a1)
  also have "... = (atomic(\<top>, r) \<squnion> atomic(\<bottom>, -r) ; \<top>) \<iinter> atomic(q, \<bottom>)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(\<top>, r) \<iinter> atomic(q, \<bottom>) \<squnion> atomic(\<bottom>, -r) ; \<top> \<iinter> atomic(q, \<bottom>) ; nil"
    by (simp add: conj.nondet_sync_distrib)
  also have "... = atomic(\<top>, r) \<iinter> atomic(q, \<bottom>) \<squnion> (atomic(\<bottom>, -r) \<iinter> atomic(q, \<bottom>)) ; \<top>"
    by (metis conj.atomic_pre_sync_atomic_pre conj_abort_left)
  also have "... = atomic(\<top> \<inter> q, r \<inter> \<bottom>) \<squnion> atomic(\<bottom> \<inter> q, -r \<inter> \<bottom>) ; \<top>"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: atomic_def)
qed

lemma rely_distrib_step_env: "rely r \<iinter> \<epsilon>(q) = \<epsilon>(q \<inter> r) \<squnion> \<epsilon>(q \<inter> -r) ; \<top>"
proof -
  have a1: "\<epsilon>(q) = atomic(\<bottom>, q)"
    by (simp add: atomic_def)
  have "rely r \<iinter> \<epsilon>(q) = (atomic(\<top>, r) \<squnion> atomic(\<bottom>, -r) ; \<top>)\<^sup>\<omega> \<iinter> atomic(\<bottom>, q)"
    by (metis rely_distrib_step_helper a1)
  also have "... = (atomic(\<top>, r) \<squnion> atomic(\<bottom>, -r) ; \<top>) \<iinter> atomic(\<bottom>, q)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(\<top>, r) \<iinter> atomic(\<bottom>, q) \<squnion> atomic(\<bottom>, -r) ; \<top> \<iinter> atomic(\<bottom>, q) ; nil"
    by (simp add: conj.nondet_sync_distrib)
  also have "... = atomic(\<top>, r) \<iinter> atomic(\<bottom>, q) \<squnion> (atomic(\<bottom>, -r) \<iinter> atomic(\<bottom>, q)) ; \<top>"
    by (metis conj.atomic_pre_sync_atomic_pre conj_abort_left)
  also have "... = atomic(\<top> \<inter> \<bottom>, r \<inter> q) \<squnion> atomic(\<bottom> \<inter> \<bottom>, -r \<inter> q) ; \<top>"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: Int_commute atomic_def)
qed

lemma rely_distrib_step_atomic: "rely r \<iinter> \<alpha>(q) = \<pi>(q) \<squnion> \<epsilon>(q \<inter> r) \<squnion> \<epsilon>(q \<inter> -r) ; \<top>"
proof -
  have "rely r \<iinter> \<alpha>(q) = (atomic(\<top>, r) \<squnion> atomic(\<bottom>, -r) ; \<top>)\<^sup>\<omega> \<iinter> atomic(q, q)"
    using atomic_general_atomic rely_distrib_step_helper by auto
  also have "... = (atomic(\<top>, r) \<squnion> atomic(\<bottom>, -r) ; \<top>) \<iinter> atomic(q, q)"
    by (metis conj.atomic_iter_distrib_atomic)
  also have "... = atomic(\<top>, r) \<iinter> atomic(q, q) \<squnion> atomic(\<bottom>, -r) ; \<top> \<iinter> atomic(q, q) ; nil"
    by (simp add: conj.nondet_sync_distrib)
  also have "... = atomic(\<top>, r) \<iinter> atomic(q, q) \<squnion> (atomic(\<bottom>, -r) \<iinter> atomic(q, q)) ; \<top>"
    by (metis conj.atomic_pre_sync_atomic_pre conj_abort_left)
  also have "... = atomic(\<top> \<inter> q, r \<inter> q) \<squnion> atomic(\<bottom> \<inter> q, -r \<inter> q) ; \<top>"
    by (metis atomic.hom_inf atomic_conj_inf inf_prod.simps)
  finally show ?thesis
    by (simp add: Int_commute atomic_def)
qed

(* Restatment of general_atomic_test_post that is easier to use with the 
   definition of invariants *)
lemma general_atomic_test_post2:
  shows "\<alpha>(r \<inter> (UNIV \<triangleright> p)) ; \<tau>(p) = \<alpha>(r \<inter> (UNIV \<triangleright> p))"
proof -
  have a1: "r \<triangleright> p = r \<inter> {(x, y). y \<in> p}"
    by (simp add: restrict_range_def)
  have a2: "UNIV \<triangleright> p = {(x, y). y \<in> p}"
    by (simp add: restrict_range_def)
  have "\<alpha>(r \<inter> (UNIV \<triangleright> p)) ; \<tau>(p) = \<alpha>(r \<triangleright> p) ; \<tau>(p)"
    by (metis a1 a2)
  also have "... = \<alpha>(r \<inter> (UNIV \<triangleright> p))"
    by (metis general_atomic_test_post a1 a2)
  finally show ?thesis .
qed

lemma step_preserve_prop:
  assumes "(p\<^sub>1 \<triangleleft> UNIV) \<inter> r \<subseteq> UNIV \<triangleright> p\<^sub>2"
  shows "\<tau>(p\<^sub>1) ; \<alpha>(r) ; \<tau>(p\<^sub>2) = \<tau>(p\<^sub>1) ; \<alpha>(r)"
proof -
  have "\<tau>(p\<^sub>1) ; \<alpha>(r) ; \<tau>(p\<^sub>2) = \<alpha>((p\<^sub>1 \<triangleleft> UNIV) \<inter> r) ; \<tau>(p\<^sub>2)"
    by (simp add: atomic_pull_test)
  also have "... = \<alpha>((p\<^sub>1 \<triangleleft> UNIV) \<inter> r \<inter> (UNIV \<triangleright> p\<^sub>2)) ; \<tau>(p\<^sub>2)"
    by (simp add: assms inf_absorb1)
  also have "... = \<alpha>((p\<^sub>1 \<triangleleft> UNIV) \<inter> r \<inter> (UNIV \<triangleright> p\<^sub>2))"
    using general_atomic_test_post2 by blast
  also have "... = \<alpha>((p\<^sub>1 \<triangleleft> UNIV) \<inter> r)"
    by (simp add: assms inf_absorb1)
  also have "... = \<tau>(p\<^sub>1) ; \<alpha>(r)"
    by (simp add: atomic_pull_test)
  finally show ?thesis .
qed

lemma evolve_preserve_test_guar_atomic:
  assumes "(p \<triangleleft> UNIV) \<inter> r \<subseteq> UNIV \<triangleright> p"
  shows "\<tau> p ; guar\<^sub>\<alpha> r ; \<tau> p = \<tau> p ; guar\<^sub>\<alpha> r"
proof -
  show ?thesis
    by (simp add: assms guar\<^sub>\<alpha>_def conj.preserve_test step_preserve_prop)
qed

lemma evolve_preserve_test_guar_atomic_conj:
  assumes "(p \<triangleleft> UNIV) \<inter> r \<subseteq> UNIV \<triangleright> p"
  shows "\<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c) ; \<tau> p = \<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c)"
proof -
  show ?thesis
    by (simp add: assms guar\<^sub>\<alpha>_def conj.maintain_test step_preserve_prop)
qed

lemma evolve_preserve_test_guar_atomic_conj_fiter:
  assumes "(p \<triangleleft> UNIV) \<inter> r \<subseteq> UNIV \<triangleright> p"
  shows "\<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c)\<^sup>\<star> = \<tau> p ; (\<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c))\<^sup>\<star>"
proof -
  show ?thesis
    by (simp add: assms guar\<^sub>\<alpha>_def conj.finite_iter_maintain_test step_preserve_prop)
qed

lemma evolve_preserve_test_guar_atomic_conj_iter:
  assumes "(p \<triangleleft> UNIV) \<inter> r \<subseteq> UNIV \<triangleright> p"
  shows "\<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c)\<^sup>\<omega> = \<tau> p ; (\<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c))\<^sup>\<omega>"
proof -
  show ?thesis
    by (simp add: assms guar\<^sub>\<alpha>_def conj.iter_maintain_test step_preserve_prop)
qed

lemma evolve_preserve_test_guar_atomic_conj_seq:
  assumes "(p \<triangleleft> UNIV) \<inter> r \<subseteq> UNIV \<triangleright> p"
  shows "\<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c\<^sub>1 ; c\<^sub>2) = \<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c\<^sub>1) ; \<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c\<^sub>2)"
proof -
  have a1: "\<tau> p ; (atomic(r, r)) = \<tau> p ; (atomic(r, r)) ; \<tau> p"
    by (simp add: assms atomic_general_atomic step_preserve_prop)
  have "\<tau> p ; (guar\<^sub>\<alpha> r \<iinter> c\<^sub>1 ; c\<^sub>2) = \<tau> p ; (atomic(r, r)\<^sup>\<omega> \<iinter> c\<^sub>1 ; c\<^sub>2)"
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def)
  also have "... = \<tau> p ; (atomic(r, r)\<^sup>\<omega> \<iinter> c\<^sub>1) ; \<tau> p ; (atomic(r, r)\<^sup>\<omega> \<iinter> c\<^sub>2)"
    by (metis conj.seq_maintain_test a1)
  finally show ?thesis
    by (simp add: atomic_general_atomic guar\<^sub>\<alpha>_def)
qed

(*

(* localise over relies and guarantees *)

text_raw \<open>\DefineSnippet{relyuniv}{\<close>
lemma localise_rely: "E\<^sup>C\<^sub>x (rely r) = rely (lib_univ x r)" (* Lemma 7 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot 
    test.hom_iso_eq test_lib test.hom_not test_top
  by (metis (full_types))

text_raw \<open>\DefineSnippet{librely}{\<close>
lemma lib_rely: "r = (E\<^sup>R\<^sub>x r) \<Longrightarrow> (rely (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (rely r))"
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot 
      test.hom_iso_eq test_lib test.hom_not test_top
  by (metis (full_types))

(* Lemma 8 - localise_gdr *)
text_raw \<open>\DefineSnippet{libguar}{\<close>
lemma localise_guar: "((E\<^sup>R\<^sub>x r) = (bool_last x r)) \<Longrightarrow> (guar (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (guar r))" (* 68 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot test.hom_iso_eq test_lib 
      test.hom_not test_top
  by (metis (full_types))

text_raw \<open>\DefineSnippet{libdem}{\<close>
lemma localise_dem: "((E\<^sup>R\<^sub>x r) = (bool_last x r)) \<Longrightarrow> (demand (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (demand r))" (* 69 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot test.hom_iso_eq test_lib 
      test.hom_not test_top
  by (metis (full_types))

lemma localise_relies: "((E\<^sup>R\<^sub>x r) = r) \<Longrightarrow> (rely (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (rely r))" (* 70 *)
  using lib_rely by blast

end *)

end
end
