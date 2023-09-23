section \<open>Parallel composition of $\pgm$ and $\epsilon$ steps defined via the flip operator\<close>

theory ParallelFlip
imports
  "PgmEnv_Commands"

begin

locale flip = pgm_env_commands (* lib_first for
  lib_first :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("F\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

definition flip :: "'a \<Rightarrow> 'a"
  where "flip c \<equiv> (if c \<in> range(\<epsilon>) then 
                        (let p = (THE p. \<epsilon> p = c) in (\<pi>(p)))
                     else undefined)"

lemma flip_def2:
  shows "flip(\<epsilon>(p)) = \<pi>(p)"
proof -
  define P where "P \<equiv> (\<lambda>p'. \<epsilon> p' = \<epsilon> p)"
  have "P p" unfolding P_def by simp
  moreover have "\<And>p'. P p' \<Longrightarrow> p' = p"
    unfolding P_def using env.hom_injective unfolding inj_def by auto
  ultimately have a1: "(THE p'. P p') = p"
    using theI by blast
  have "flip (\<epsilon> p) = (let p' = (THE p'. \<epsilon> p' = (\<epsilon> p)) in (\<pi>(p')))"
    unfolding flip_def by auto
  also have "... = (\<pi> p)"
    using env.hom_injective a1 unfolding P_def by simp
  finally show ?thesis by simp
qed

end

locale parallel_flip = pgm_env_commands + flip +
  assumes env_par_env_axiom: "\<epsilon>(p) \<parallel> \<epsilon>(q) = \<epsilon>(p) \<sqinter> \<epsilon>(q)"  
  assumes pgm_par_pgm:   "\<pi>(p) \<parallel> \<pi>(q) = \<bottom>"
  assumes env_par_pgm_axiom:  "\<epsilon>(p) \<parallel> \<pi>(q) = flip(\<epsilon>(p)) \<sqinter> \<pi>(q)" 

begin

lemma pgm_com_par_pgm_com: "\<pi>(p);c \<parallel> \<pi>(q);d = \<bottom>"
  by (metis par.atomic_pre_sync_atomic_pre pgm_atomic pgm_par_pgm seq_magic_left)

lemma env_com_par_pgm_com:  "\<epsilon>(p);c \<parallel> \<pi>(q);d = \<pi>(p \<sqinter> q);(c \<parallel> d)"
  by (metis env_atomic env_par_pgm_axiom flip_def2 par.atomic_pre_sync_atomic_pre pgm_atomic pgm.hom_inf) 

lemma env_com_par_env_com: "\<epsilon>(p);c \<parallel> \<epsilon>(q);d =  \<epsilon>(p \<sqinter> q);(c \<parallel> d)"
  by (metis env_atomic env.hom_inf env_par_env_axiom par.atomic_pre_sync_atomic_pre)

lemma pgm_par_Env_com: "\<pi>(p);c \<parallel> \<E>;d = \<pi>(p);(c \<parallel> d)"
  by (metis Env_def env_com_par_pgm_com inf_top.left_neutral par.sync_commute)

lemma pgmenv_par_pgmenv: "(\<pi>(r) \<squnion> \<epsilon>(\<top>)) \<parallel> (\<pi>(r) \<squnion> \<epsilon>(\<top>)) = (\<pi>(r) \<squnion> \<epsilon>(\<top>))"
proof -
  have a1: "\<pi>(r)\<parallel>\<epsilon>(\<top>) = \<pi>(r)"
    by (metis abel_semigroup.commute Env_def par.comm.abel_semigroup_axioms
          par.atomic_sync_identity pgm_atomic)
  have a2: "\<epsilon>(\<top>)\<parallel>\<pi>(r) = \<pi>(r)"
    by (metis a1 par_commute)
  have a3: "\<pi>(r)\<parallel>\<pi>(r) = \<bottom>"
    using pgm_par_pgm by blast
  have "(\<pi>(r) \<squnion> \<epsilon>(\<top>)) \<parallel> (\<pi>(r) \<squnion> \<epsilon>(\<top>)) = (\<pi>(r)\<parallel>\<pi>(r)) \<squnion> (\<pi>(r)\<parallel>\<epsilon>(\<top>)) \<squnion> (\<epsilon>(\<top>)\<parallel>\<pi>(r)) \<squnion> (\<epsilon>(\<top>)\<parallel>\<epsilon>(\<top>))"
    using par.nondet_sync_product by simp
  also have "... = (\<pi>(r) \<squnion> \<epsilon>(\<top>))"    
    using env_par_env_axiom a1 a2 a3 by simp
  finally show ?thesis by simp
qed

(* Helper for the next few lemmas *)
lemma pgm_env_parallel:
  shows "(\<pi>(g\<^sub>1) \<squnion> \<epsilon>(r\<^sub>1)) \<parallel> (\<pi>(g\<^sub>2) \<squnion> \<epsilon>(r\<^sub>2)) = \<pi>((g\<^sub>1 \<sqinter> r\<^sub>2) \<squnion> (r\<^sub>1 \<sqinter> g\<^sub>2)) \<squnion> \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2)"
proof -
  have "(\<pi>(g\<^sub>1) \<squnion> \<epsilon>(r\<^sub>1)) \<parallel> (\<pi>(g\<^sub>2) \<squnion> \<epsilon>(r\<^sub>2)) = (\<pi>(g\<^sub>1) \<parallel> \<pi>(g\<^sub>2)) \<squnion> (\<pi>(g\<^sub>1) \<parallel> \<epsilon>(r\<^sub>2)) \<squnion> (\<epsilon>(r\<^sub>1) \<parallel> \<pi>(g\<^sub>2)) \<squnion> (\<epsilon>(r\<^sub>1) \<parallel> \<epsilon>(r\<^sub>2))"
    by (simp add: par.nondet_sync_product)
  also have "... = \<bottom> \<squnion> \<pi>(g\<^sub>1 \<sqinter> r\<^sub>2) \<squnion> \<pi>(r\<^sub>1 \<sqinter> g\<^sub>2) \<squnion> \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2)"
    by (metis env.hom_inf env_par_env_axiom env_par_pgm_axiom flip_def2 par_commute pgm.hom_inf pgm_par_pgm)
  finally show ?thesis
    by simp
qed

lemma par_atomic_idempotent: 
  assumes a_def: "a = \<pi>(g) \<squnion> \<epsilon>(r)"
  assumes g_subset: "g \<le> r"
  shows "a \<parallel> a = a"
proof -
  have "a \<parallel> a = (\<pi>(g) \<squnion> \<epsilon>(r)) \<parallel> (\<pi>(g) \<squnion> \<epsilon>(r))"
    by (metis a_def)
  also have "... = \<pi>(g \<sqinter> r) \<squnion> \<epsilon>(r)"
    by (simp add: inf_commute pgm_env_parallel)
  also have "... = \<pi>(g) \<squnion> \<epsilon>(r)"
    by (metis g_subset inf.orderE)
  also have "... = a"
    by (metis a_def)
  finally show ?thesis .
qed

lemma conj_par_interchange_atomic:
  assumes a1_def [simp]: "a\<^sub>1 = atomic(g\<^sub>1, r\<^sub>1)"
  assumes a2_def [simp]: "a\<^sub>2 = atomic(g\<^sub>2, r\<^sub>2)"
  assumes b1_def [simp]: "b\<^sub>1 = atomic(h\<^sub>1, s\<^sub>1)"
  assumes b2_def [simp]: "b\<^sub>2 = atomic(h\<^sub>2, s\<^sub>2)"
  shows "(a\<^sub>1 \<parallel> a\<^sub>2) \<iinter> (b\<^sub>1 \<parallel> b\<^sub>2) = ((a\<^sub>1 \<iinter> b\<^sub>1) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>2)) \<squnion> ((a\<^sub>1 \<iinter> b\<^sub>2) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>1))"
proof -
  have a1_par_a2: "a\<^sub>1 \<parallel> a\<^sub>2 = \<pi>((g\<^sub>1 \<sqinter> r\<^sub>2) \<squnion> (r\<^sub>1 \<sqinter> g\<^sub>2)) \<squnion> \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2)"
    by (simp add: pgm_env_parallel atomic_def)
  have b1_par_b2: "b\<^sub>1 \<parallel> b\<^sub>2 = \<pi>((h\<^sub>1 \<sqinter> s\<^sub>2) \<squnion> (s\<^sub>1 \<sqinter> h\<^sub>2)) \<squnion> \<epsilon>(s\<^sub>1 \<sqinter> s\<^sub>2)"
    by (simp add: pgm_env_parallel atomic_def)
  have lhs: "(a\<^sub>1 \<parallel> a\<^sub>2) \<iinter> (b\<^sub>1 \<parallel> b\<^sub>2) = \<pi>((g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2) \<squnion>
                                      (g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2) \<squnion>
                                      (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2) \<squnion>
                                      (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2)) \<squnion>
                                    \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> s\<^sub>2)"
    by (smt (verit, del_insts) a1_par_a2 b1_par_b2 conj.nondet_sync_product env_conj_env local.conj_assoc pgm.hom_sup pgm_conj_pgm pgmenv_conj_pgmenv)
  
  have a1_b1_par_a2_b2: "(a\<^sub>1 \<iinter> b\<^sub>1) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>2) = \<pi>((g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2) \<squnion>
                                                  (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2)) \<squnion>
                                                \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> s\<^sub>2)"
  proof -
    have "(a\<^sub>1 \<iinter> b\<^sub>1) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>2) = (\<pi>(g\<^sub>1 \<sqinter> h\<^sub>1) \<squnion> \<epsilon>(r\<^sub>1 \<sqinter> s\<^sub>1)) \<parallel> (\<pi>(g\<^sub>2 \<sqinter> h\<^sub>2) \<squnion> \<epsilon>(r\<^sub>2 \<sqinter> s\<^sub>2))"
      by (simp add: atomic_def pgmenv_conj_pgmenv)
    also have "... = \<pi>(((g\<^sub>1 \<sqinter> h\<^sub>1) \<sqinter> (r\<^sub>2 \<sqinter> s\<^sub>2)) \<squnion> ((r\<^sub>1 \<sqinter> s\<^sub>1) \<sqinter> (g\<^sub>2 \<sqinter> h\<^sub>2))) \<squnion> \<epsilon>((r\<^sub>1 \<sqinter> s\<^sub>1) \<sqinter> (r\<^sub>2 \<sqinter> s\<^sub>2))"
      by (metis pgm_env_parallel)
    finally show ?thesis
      by (simp add: inf_commute inf_left_commute)
  qed
  have a1_b2_par_a2_b1: "(a\<^sub>1 \<iinter> b\<^sub>2) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>1) = \<pi>((g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2) \<squnion>
                                                  (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2)) \<squnion>
                                                \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> s\<^sub>2)"
  proof -
    have "(a\<^sub>1 \<iinter> b\<^sub>2) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>1) = (\<pi>(g\<^sub>1 \<sqinter> h\<^sub>2) \<squnion> \<epsilon>(r\<^sub>1 \<sqinter> s\<^sub>2)) \<parallel> (\<pi>(g\<^sub>2 \<sqinter> h\<^sub>1) \<squnion> \<epsilon>(r\<^sub>2 \<sqinter> s\<^sub>1))"
      by (simp add: atomic_def pgmenv_conj_pgmenv)
    also have "... = \<pi>(((g\<^sub>1 \<sqinter> h\<^sub>2) \<sqinter> (r\<^sub>2 \<sqinter> s\<^sub>1)) \<squnion> ((r\<^sub>1 \<sqinter> s\<^sub>2) \<sqinter> (g\<^sub>2 \<sqinter> h\<^sub>1))) \<squnion> \<epsilon>((r\<^sub>1 \<sqinter> s\<^sub>2) \<sqinter> (r\<^sub>2 \<sqinter> s\<^sub>1))"
      by (metis pgm_env_parallel)
    finally show ?thesis
      by (simp add: inf_commute inf_left_commute)
  qed
  
  have rhs: "((a\<^sub>1 \<iinter> b\<^sub>1) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>2)) \<squnion> ((a\<^sub>1 \<iinter> b\<^sub>2) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>1))  = \<pi>((g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2) \<squnion>
                                                                  (g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2) \<squnion>
                                                                  (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2) \<squnion>
                                                                  (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2)) \<squnion>
                                                                \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> s\<^sub>2)"
  proof -
    have "((a\<^sub>1 \<iinter> b\<^sub>1) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>2)) \<squnion> ((a\<^sub>1 \<iinter> b\<^sub>2) \<parallel> (a\<^sub>2 \<iinter> b\<^sub>1)) = (\<pi>((g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2) \<squnion> (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2)) \<squnion> \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> s\<^sub>2)) \<squnion>
                                                            (\<pi>((g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2) \<squnion> (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2)) \<squnion> \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> s\<^sub>2))"
      by (metis a1_b1_par_a2_b2 a1_b2_par_a2_b1)
    also have "... = (\<pi>((g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2) \<squnion> (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2)) \<squnion> \<pi>((g\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> h\<^sub>2) \<squnion> (r\<^sub>1 \<sqinter> g\<^sub>2 \<sqinter> h\<^sub>1 \<sqinter> s\<^sub>2)) \<squnion> \<epsilon>(r\<^sub>1 \<sqinter> r\<^sub>2 \<sqinter> s\<^sub>1 \<sqinter> s\<^sub>2))"
      by (simp add: sup_commute sup_left_commute)
    finally show ?thesis
      by (simp add: sup_commute sup_left_commute)
  qed
  show ?thesis by (metis lhs rhs)
qed

lemma par_distrib_if_idempotent_atomic:
  assumes a_def [simp]: "a = atomic(g, r)"
  assumes b1_def [simp]: "b\<^sub>1 = atomic(h\<^sub>1, s\<^sub>1)"
  assumes b2_def [simp]: "b\<^sub>2 = atomic(h\<^sub>2, s\<^sub>2)"
  assumes a_idem: "a \<parallel> a = a"
  shows "a \<iinter> (b\<^sub>1 \<parallel> b\<^sub>2) = (a \<iinter> b\<^sub>1) \<parallel> (a \<iinter> b\<^sub>2)"
proof -
  have "a \<iinter> (b\<^sub>1 \<parallel> b\<^sub>2) = (a \<parallel> a) \<iinter> (b\<^sub>1 \<parallel> b\<^sub>2)"
    by (metis a_idem)
  also have "... = ((a \<iinter> b\<^sub>1) \<parallel> (a \<iinter> b\<^sub>2)) \<squnion> ((a \<iinter> b\<^sub>2) \<parallel> (a \<iinter> b\<^sub>1))"
    by (metis a_def b1_def b2_def conj_par_interchange_atomic)
  finally show ?thesis
    by (simp add: par_commute)
qed

lemma par_distrib_finite_if_idempotent_helper:
  shows "\<tau> q \<parallel> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. atomic (b\<^sub>m) ; c\<^sub>m) = \<bottom>"
proof -
  define f where f_def: "f \<equiv> \<lambda> (b\<^sub>m, c\<^sub>m). atomic (b\<^sub>m) ; c\<^sub>m" 

  have a1: "\<tau> q \<parallel> \<bottom> = \<bottom>"
    by (metis inf_bot_right test.hom_bot test_par_test)
  have a2: "\<tau> q \<parallel> (\<Squnion>m\<in>M. f(m)) = (\<Squnion>m\<in>M. \<tau> q \<parallel> f(m))"
    using a1 par.non_aborting_distrib2 by blast
  have "\<tau> q \<parallel> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. atomic (b\<^sub>m) ; c\<^sub>m) = \<tau> q \<parallel> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m)))"
    using f_def by fastforce
  also have "... = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. \<tau> q \<parallel> f((b\<^sub>m, c\<^sub>m)))"
    by (simp add: a2)
  also have "... = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. \<tau> q \<parallel> atomic (b\<^sub>m) ; c\<^sub>m)"
    using f_def by fastforce
  also have "... = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. \<bottom>)"
    by (simp add: par.test_sync_atomic_pre)
  also have "... = \<bottom>"
    by simp
  finally show ?thesis .
qed

lemma par_distrib_finite_if_idempotent_helper_2:
  shows "(\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m) \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m) = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))"
proof -
  define f where f_def: "f \<equiv> \<lambda> (b1\<^sub>m, c1\<^sub>m). (atomic (b1\<^sub>m)) ; c1\<^sub>m" 

  have a1: "(\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m) \<parallel> \<bottom> = \<bottom>"
    by (metis par.expanded_form_sync_magic)
  have a2: "\<forall> b1\<^sub>m c1\<^sub>m. f((b1\<^sub>m, c1\<^sub>m)) \<parallel> \<bottom> = \<bottom>"
  proof -
    {
      fix b1\<^sub>m c1\<^sub>m
      have "f((b1\<^sub>m, c1\<^sub>m)) \<parallel> \<bottom> = \<bottom>"
      proof -
        have "f((b1\<^sub>m, c1\<^sub>m)) \<parallel> \<bottom> = (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> \<bottom>"
          using f_def by fastforce
        also have "... = \<bottom>"
          by (metis atomic_test_par par_commute test.hom_bot)
        finally show ?thesis .
      qed
    }
    then show ?thesis
      by simp
  qed

  have "(\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m) \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m) = (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m) \<parallel> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. f((b1\<^sub>m, c1\<^sub>m)))" 
    using f_def par.sync_commute by fastforce
  also have "... = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m) \<parallel> f((b1\<^sub>m, c1\<^sub>m)))"
    by (simp add: a1 par.non_aborting_distrib2)
  also have "... = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. f((b1\<^sub>m, c1\<^sub>m)) \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. f((b2\<^sub>m, c2\<^sub>m))))"
    using f_def par.sync_commute by fastforce
  also have "... = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. f((b1\<^sub>m, c1\<^sub>m)) \<parallel> f((b2\<^sub>m, c2\<^sub>m))))"
    by (simp add: par.non_aborting_distrib2 a2)
  also have "... = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))"
    using f_def by fastforce
  finally show ?thesis .
qed

lemma par_distrib_finite_if_idempotent_helper_3:
  assumes a_def [simp]: "a = atomic(g, r)"
  shows "(a \<^sup>;^ i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)) = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a \<^sup>;^ i) \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
proof -
  have a_iter_conj_magic: "a\<^sup>\<omega> \<iinter> \<bottom> = \<bottom>"
  proof -
    have b1: "a = atomic(g, r) \<squnion> atomic(\<bottom>) ; \<top>"
      by simp
    show ?thesis
      by (metis conj.pseudo_atomic_fixed_points_pseudo_iter b1 conj.atomic_distributing_sync_magic)
  qed
  have iter_ref_i: "a\<^sup>\<omega> \<ge> (a \<^sup>;^ i)"
    by (simp add: iter_i)
  have ai_conj_magic: "(a \<^sup>;^ i) \<iinter> \<bottom> = \<bottom>"
    by (metis a_iter_conj_magic iter_ref_i conj.nondet_sync_distrib conj_to_inf inf_bot_right sup.absorb_iff1 sup.absorb_iff2)

  define f where f_def: "f \<equiv> \<lambda> (b1\<^sub>m, c1\<^sub>m). (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)" 
  have dist1: "(a \<^sup>;^ i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. f(b1\<^sub>m, c1\<^sub>m)) = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (a \<^sup>;^ i) \<iinter> f(b1\<^sub>m, c1\<^sub>m))"
    using ai_conj_magic conj.non_aborting_distrib2 by auto
  {
    fix b1\<^sub>m
    fix c1\<^sub>m
    have "(a \<^sup>;^ i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m) = (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a \<^sup>;^ i) \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))"
    proof -
      define g where g_def: "g \<equiv> \<lambda> (b2\<^sub>m, c2\<^sub>m). (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m"
      have b1: "(a \<^sup>;^ i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. g(b2\<^sub>m, c2\<^sub>m)) = (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a \<^sup>;^ i) \<iinter> g(b2\<^sub>m, c2\<^sub>m))"
        using ai_conj_magic conj.non_aborting_distrib2 by auto
      have "(a \<^sup>;^ i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m) = (a \<^sup>;^ i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. g(b2\<^sub>m, c2\<^sub>m))"
        using g_def by fastforce
      also have "... = (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a \<^sup>;^ i) \<iinter> g(b2\<^sub>m, c2\<^sub>m))"
        using ai_conj_magic conj.non_aborting_distrib2 by auto
      finally show ?thesis
        using g_def by fastforce
     qed
  }
  then have dist2: "\<And>b1\<^sub>m c1\<^sub>m.(a \<^sup>;^ i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m) = (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a \<^sup>;^ i) \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))"
    by blast

  have "(a \<^sup>;^ i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)) = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (a \<^sup>;^ i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))"
    using dist1 f_def by fastforce
  then show ?thesis
    using dist2 by presburger
qed

lemma par_distrib_finite_if_idempotent_helper_4:
  shows "nil \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m) = \<bottom>"
proof -
  obtain b where b_def: "atomic b = atomic (b1\<^sub>m) \<parallel> atomic (b2\<^sub>m)"
    by (metis par.atomic_sync)
  have "nil \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m) = nil \<iinter> ((atomic (b1\<^sub>m) \<parallel> atomic (b2\<^sub>m)) ; (c1\<^sub>m \<parallel> c2\<^sub>m))"
    by (metis conj.nil_sync_atomic_pre par.atomic_pre_sync_atomic_pre par.atomic_sync)
  also have "... =  nil \<iinter> (atomic b ; (c1\<^sub>m \<parallel> c2\<^sub>m))"
    by (metis b_def)
  also have "... = \<bottom>"
    by (simp add: conj.nil_sync_atomic_pre)
  finally show ?thesis .
qed

lemma par_distrib_finite_if_idempotent_helper_5:
  assumes a_def [simp]: "a = atomic(g, r)"
  assumes a_idem: "a = a \<parallel> a"
  assumes induction_hyps: "(a \<^sup>;^ i) \<iinter> (c1\<^sub>m \<parallel> c2\<^sub>m) = ((a \<^sup>;^ i) \<iinter> c1\<^sub>m) \<parallel> ((a \<^sup>;^ i) \<iinter> c2\<^sub>m)"
  shows "(a ; (a \<^sup>;^ i)) \<iinter> ((atomic (b1\<^sub>m) \<parallel> atomic (b2\<^sub>m)) ; (c1\<^sub>m \<parallel> c2\<^sub>m)) = ((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> atomic (b2\<^sub>m) ; c2\<^sub>m)"
proof -
  (* Need to do this to use par_distrib_if_idempotent_atomic *)
  obtain h1 s1 where [simp]: "b1\<^sub>m = (h1, s1)"
    by fastforce
  obtain h2 s2 where [simp]: "b2\<^sub>m = (h2, s2)"
    by fastforce
  have a1: "a \<iinter> (atomic (b1\<^sub>m) \<parallel> atomic (b2\<^sub>m)) = (a \<iinter> atomic (b1\<^sub>m)) \<parallel> (a \<iinter> atomic (b2\<^sub>m))"
    using par_distrib_if_idempotent_atomic a_def a_idem by auto

  (* Needed to use par.atomic_pre_sync_atomic_pre *)
  obtain p where a_conj_b1: "a \<iinter> atomic (b1\<^sub>m) = atomic p"
    using a_def conj.atomic_sync by blast
  obtain q where a_conj_b2: "a \<iinter> atomic (b2\<^sub>m) = atomic q"
    using a_def conj.atomic_sync by blast

  have "(a ; (a \<^sup>;^ i)) \<iinter> ((atomic (b1\<^sub>m) \<parallel> atomic (b2\<^sub>m)) ; (c1\<^sub>m \<parallel> c2\<^sub>m)) = (a \<iinter> (atomic (b1\<^sub>m) \<parallel> atomic (b2\<^sub>m))) ; ((a \<^sup>;^ i) \<iinter> (c1\<^sub>m \<parallel> c2\<^sub>m))"
    by (metis assms(1) conj.atomic_pre_sync_atomic_pre par.atomic_sync)
  also have "... = ((a \<iinter> atomic (b1\<^sub>m)) \<parallel> (a \<iinter> atomic (b2\<^sub>m))) ; (((a \<^sup>;^ i) \<iinter> c1\<^sub>m) \<parallel> ((a \<^sup>;^ i) \<iinter> c2\<^sub>m))"
    by (metis a1 induction_hyps)
  also have "... = (a \<iinter> atomic (b1\<^sub>m)) ; ((a \<^sup>;^ i) \<iinter> c1\<^sub>m) \<parallel> (a \<iinter> atomic (b2\<^sub>m)) ; ((a \<^sup>;^ i) \<iinter> c2\<^sub>m)"
    using a_conj_b1 a_conj_b2 par.atomic_pre_sync_atomic_pre by auto
  also have "... = ((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> atomic (b2\<^sub>m) ; c2\<^sub>m)"
    by (simp add: conj.atomic_pre_sync_atomic_pre)
  finally show ?thesis .
qed

lemma par_distrib_finite_if_idempotent_helper_6:
  assumes a_def [simp]: "a = atomic(g, r)"
  shows "(a \<^sup>;^ Suc i) \<iinter> \<tau> q = \<bottom>"
proof -
  have a1: "(a \<^sup>;^ Suc i) \<iinter> \<tau> q = a ; (a \<^sup>;^ i) \<iinter> \<tau> q"
    by simp
  have a2: "(a \<^sup>;^ Suc i) \<iinter> \<tau> q \<le> Atomic ; (a \<^sup>;^ i) \<iinter> nil"
    by (simp add: a1 conj.test_sync_atomic_pre local.conj_commute)
  have "(a \<^sup>;^ Suc i) \<iinter> \<tau> q = \<bottom>"
    by (metis a2 conj.nil_sync_atomic_pre inf.order_iff inf.syncid_atomic inf_bot_right local.conj_commute)
  then show ?thesis
    by auto
qed

lemma par_distrib_finite_if_idempotent_helper_7:
  assumes a_def [simp]: "a = atomic(g, r)" 
  shows "(\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. ((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> atomic (b2\<^sub>m) ; c2\<^sub>m))) = ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))"
proof -
  have ai_conj_magic: "(a \<^sup>;^ Suc i) \<iinter> \<bottom> = \<bottom>"
    by (metis a_def par_distrib_finite_if_idempotent_helper_6 local.conj.left_idem)
  
  {
    fix b1\<^sub>m
    fix c1\<^sub>m
    have "(\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. ((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> atomic (b2\<^sub>m) ; c2\<^sub>m)) = ((a \<^sup>;^ Suc i) \<iinter> (atomic (b1\<^sub>m) ; c1\<^sub>m)) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m) ; c2\<^sub>m)))"
    proof -
      define g where g_def: "g \<equiv> \<lambda> (b2\<^sub>m, c2\<^sub>m). atomic (b2\<^sub>m) ; c2\<^sub>m"
      define h where h_def: "h \<equiv> \<lambda> (b2\<^sub>m, c2\<^sub>m). (a \<^sup>;^ Suc i) \<iinter> g(b2\<^sub>m, c2\<^sub>m)"
      define k where k_def: "k = (((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m))"

      have par_magic: "k \<parallel> \<bottom> = \<bottom>"
        by (smt (verit, best) k_def assms conj.sync_nil_magic_takes_step conj.test_sync_atomic_pre local.conj_assoc local.conj_commute par.sync_nil_magic_takes_step par.test_sync_post seq_power_Suc test.hom_bot test_seq_magic test_top)

      have "(\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. ((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> atomic (b2\<^sub>m) ; c2\<^sub>m)) = (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. k \<parallel> h(b2\<^sub>m, c2\<^sub>m))"
        using g_def h_def k_def by auto
      also have "... = (\<Squnion>m\<in>M2. k \<parallel> h(m))"
        by simp
      also have "... = k \<parallel> (\<Squnion>m\<in>M2. h(m))"
        by (metis par.non_aborting_distrib2 par_magic)
      also have "... = k \<parallel> (\<Squnion>m\<in>M2. (a \<^sup>;^ Suc i) \<iinter> g(m))"
        using h_def by auto
      also have "... = k \<parallel> ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. g(b2\<^sub>m, c2\<^sub>m)))"
        by (metis conj.non_aborting_distrib2 case_prod_eta ai_conj_magic)
      finally show ?thesis
        using g_def k_def by auto
     qed
  }
  then have dist1: "\<And>b1\<^sub>m c1\<^sub>m. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. ((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> atomic (b2\<^sub>m) ; c2\<^sub>m)) = ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m) ; c2\<^sub>m))) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> (atomic (b1\<^sub>m) ; c1\<^sub>m))"
    by (simp add: par_commute)

  define f where f_def: "f \<equiv> \<lambda> (b1\<^sub>m, c1\<^sub>m). (atomic (b1\<^sub>m) ; c1\<^sub>m)"
  define h where h_def: "h \<equiv> \<lambda> (b1\<^sub>m, c1\<^sub>m). (a \<^sup>;^ Suc i) \<iinter> f(b1\<^sub>m, c1\<^sub>m)"
  define k where k_def: "k = (a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m) ; c2\<^sub>m))"

  have par_magic: "k \<parallel> \<bottom> = \<bottom>"
  proof -
    define h where h_def: "h \<equiv> \<lambda> (b2\<^sub>m, c2\<^sub>m). atomic (b2\<^sub>m) ; c2\<^sub>m"
    define j where j_def: "j = Atomic ; \<top>"
    define l where l_def: "l = a ; \<top>"
    have a1: "(a \<^sup>;^ Suc i) \<iinter> (\<Squnion>m\<in>M2. j) = (\<Squnion>m\<in>M2. (a \<^sup>;^ Suc i) \<iinter> j)"
      by (metis SUP_constant ai_conj_magic)
    have a2: "\<forall> m. h(m) \<le> Atomic ; \<top>"
      by (simp add: h_def conj.nil_sync_atomic_pre conj.sync_nil_magic_takes_step_reverse local.conj_commute)
    have a3: "(\<Squnion>m\<in>M2. h(m)) \<le> (\<Squnion>m\<in>M2. Atomic ; \<top>)"
      by (simp add: SUP_constant SUP_le_iff a2)
    have a4: "(a \<^sup>;^ Suc i) \<iinter> Atomic ; \<top> = a ; \<top>"
    proof -
      have "(a \<^sup>;^ Suc i) \<iinter> Atomic ; \<top> = a ; (a \<^sup>;^ i) \<iinter> Atomic ; \<top>"
        by simp
      also have "... = (a \<iinter> Atomic) ; ((a \<^sup>;^ i) \<iinter> \<top>)"
        by (simp add: Atomic_def conj.atomic_pre_sync_atomic_pre) 
      finally show ?thesis
        by (simp add: local.conj_commute par.conj_atomic_sync_identity)
    qed
    have a5: "l \<parallel> \<bottom> = \<bottom>"
    proof -
      have "l \<parallel> \<bottom> = \<tau> \<bottom> \<parallel> atomic(g, r) ; \<top>"
        by (simp add: par_commute l_def)
      then show ?thesis
        by (metis par.test_sync_atomic_pre)
    qed
    have a6: "\<bottom> \<parallel> (\<Squnion>m\<in>M2. l) =  (\<Squnion>m\<in>M2. \<bottom> \<parallel> l)"
      by (metis SUP_const Sup_empty a5 antisym bot.extremum image_empty par.sync_mono_right par_commute)

    have b1: "k \<parallel> \<bottom> = ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>m\<in>M2. h(m))) \<parallel> \<bottom>"
      using k_def h_def by auto
    have b2: "k \<parallel> \<bottom> \<le> ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>m\<in>M2. j)) \<parallel> \<bottom>"
      by (simp add: b1 a3 conj.sync_mono_right par.sync_mono j_def)
    have b3: "k \<parallel> \<bottom> \<le> \<bottom> \<parallel> (\<Squnion>m\<in>M2. (a \<^sup>;^ Suc i) \<iinter> j) "
      using a1 b2 par_commute by auto
    have b4: "k \<parallel> \<bottom> \<le> \<bottom> \<parallel> (\<Squnion>m\<in>M2. l)"
      using b3 j_def l_def a4 by auto
    show ?thesis
      using a5 a6 b4 bot.extremum_unique par_commute by auto
  qed

  have "(\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. ((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> atomic (b2\<^sub>m) ; c2\<^sub>m))) = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m) ; c2\<^sub>m))) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> (atomic (b1\<^sub>m) ; c1\<^sub>m)))"
    using dist1 by auto
  also have "... = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. k \<parallel> h(b1\<^sub>m, c1\<^sub>m))"
    using f_def h_def k_def by auto
  also have "... = (\<Squnion>m\<in>M1. k \<parallel> h(m))"
    by simp
  also have "... = k \<parallel> (\<Squnion>m\<in>M1. h(m))"
    by (metis par_magic par.non_aborting_distrib2)
  also have "... = k \<parallel> (\<Squnion>m\<in>M1. (a \<^sup>;^ Suc i) \<iinter> f(m))"
    using h_def by auto
  also have "... = k \<parallel> ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. f(b1\<^sub>m, c1\<^sub>m)))"
    by (metis ai_conj_magic conj.non_aborting_distrib2 case_prod_eta)
  finally show ?thesis
    by (simp add: f_def k_def par_commute)
qed

lemma par_distrib_finite_if_idempotent_forall:
  assumes a_def [simp]: "a = atomic(g, r)" 
  assumes a_idem: "a = a \<parallel> a"
  shows "\<forall>c\<^sub>1 c\<^sub>2. (a \<^sup>;^ i) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) = ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2)"
proof (induct i)
  case 0
  {
    fix c\<^sub>1
    fix c\<^sub>2
    obtain p1 q1 M1 where c1_expanded: "c\<^sub>1 = \<lbrace>p1\<rbrace> ; (\<tau> q1 \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m))"
      using par.expanded_form by blast
    obtain p2 q2 M2 where c2_expanded: "c\<^sub>2 = \<lbrace>p2\<rbrace> ; (\<tau> q2 \<squnion> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))"
      using par.expanded_form by blast
  
    have main_proof: "(a \<^sup>;^ 0) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) = ((a \<^sup>;^ 0) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ 0) \<iinter> c\<^sub>2)"
    proof -
      have dist1: "nil \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)) = \<bottom>"
      proof -
        have "nil \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)) = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. nil \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
          by (metis par_distrib_finite_if_idempotent_helper_3 seq_power_0)
        also have "... = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. \<bottom>))"
          by (simp add: par_distrib_finite_if_idempotent_helper_4)
        also have "... = \<bottom>"
          by simp
        finally show ?thesis .
      qed
    
      have "(a \<^sup>;^ 0) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) = nil \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)"
        by (simp)
      also have "... = nil \<iinter> (\<lbrace>p1\<rbrace> ; (\<tau> q1 \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)) \<parallel> \<lbrace>p2\<rbrace> ; (\<tau> q2 \<squnion> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (metis c1_expanded c2_expanded)
      also have "... = nil \<iinter> \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; ((\<tau> q1 \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)) \<parallel> (\<tau> q2 \<squnion> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (metis (full_types) c2_expanded par.assert_distrib par_commute seq_assoc)
      also have "... = nil \<iinter> \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (
          (\<tau> q1 \<parallel> \<tau> q2) 
        \<squnion> (\<tau> q1 \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))
        \<squnion> ((\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m) \<parallel> \<tau> q2) 
        \<squnion> ((\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m) \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))
        )"
        by (simp add: par.nondet_sync_product)
      also have "... = nil \<iinter> \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; ((\<tau> q1 \<parallel> \<tau> q2) \<squnion> ((\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m) \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (simp add: par_distrib_finite_if_idempotent_helper par.sync_commute)
      also have "... = nil \<iinter> \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; ((\<tau> q1 \<parallel> \<tau> q2) \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (simp add: par_distrib_finite_if_idempotent_helper_2)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (nil \<iinter> ((\<tau> q1 \<parallel> \<tau> q2) \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        by (simp add: assert_seq_assert conj.assert_command_sync_command)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (nil \<iinter> (\<tau> q1 \<parallel> \<tau> q2) \<squnion> nil \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (simp add: conj.sync_nondet_distrib)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; ((\<tau> q1 \<parallel> \<tau> q2) \<squnion> nil \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (metis conj.nil_sync_test_pre seq_nil_left test_conj_to_inf test_inf_eq_seq test_par_test test_top)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (\<tau> q1 \<parallel> \<tau> q2)"
        by (simp add: dist1)
      also have "... = (\<lbrace>p1\<rbrace> ; \<tau> q1) \<parallel> (\<lbrace>p2\<rbrace> ; \<tau> q2)"
        by (metis par.assert_distrib par_commute seq_assoc)
      also have "... = (nil \<iinter> c\<^sub>1) \<parallel> (nil \<iinter> c\<^sub>2)"
        by (metis conj.expanded_test c1_expanded c2_expanded)
      finally show ?thesis
        by simp
    qed
  }
  then show ?case
    by simp
next
  case (Suc i)
  {
    fix c\<^sub>1
    fix c\<^sub>2
    obtain p1 q1 M1 where c1_expanded: "c\<^sub>1 = \<lbrace>p1\<rbrace> ; (\<tau> q1 \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m))"
    using par.expanded_form by blast
    obtain p2 q2 M2 where c2_expanded: "c\<^sub>2 = \<lbrace>p2\<rbrace> ; (\<tau> q2 \<squnion> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))"
      using par.expanded_form by blast
  
    have dist1: "(a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)) = (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a \<^sup>;^ Suc i) \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
      using par_distrib_finite_if_idempotent_helper_3 a_def by blast
    have induction_hyps: "\<forall>c1\<^sub>m c2\<^sub>m. (a \<^sup>;^ i) \<iinter> (c1\<^sub>m \<parallel> c2\<^sub>m) = ((a \<^sup>;^ i) \<iinter> c1\<^sub>m) \<parallel> ((a \<^sup>;^ i) \<iinter> c2\<^sub>m)"
      using Suc.hyps by auto
    have ai_conj_q1: "(a \<^sup>;^ Suc i) \<iinter> \<tau> q1 = \<bottom>"
      by (metis par_distrib_finite_if_idempotent_helper_6 a_def)
    have ai_conj_q2: "(a \<^sup>;^ Suc i) \<iinter> \<tau> q2 = \<bottom>"
      by (metis par_distrib_finite_if_idempotent_helper_6 a_def)

    have main_proof: "(a \<^sup>;^ Suc i) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) = ((a \<^sup>;^ Suc i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> c\<^sub>2)"
    proof -
      have "(a \<^sup>;^ Suc i) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) = (a ; (a \<^sup>;^ i)) \<iinter> (\<lbrace>p1\<rbrace> ; (\<tau> q1 \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)) \<parallel> \<lbrace>p2\<rbrace> ; (\<tau> q2 \<squnion> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (simp add: c1_expanded c2_expanded)
      also have "... = (a ; (a \<^sup>;^ i)) \<iinter> \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; ((\<tau> q1 \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)) \<parallel> (\<tau> q2 \<squnion> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (smt (verit) par.assert_distrib par_commute seq_assoc)
      also have "... = (a ; (a \<^sup>;^ i)) \<iinter> \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (
          (\<tau> q1 \<parallel> \<tau> q2) 
        \<squnion> (\<tau> q1 \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))
        \<squnion> ((\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m) \<parallel> \<tau> q2) 
        \<squnion> ((\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m) \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))
        )"
        by (simp add: par.nondet_sync_product)
      also have "... = (a ; (a \<^sup>;^ i)) \<iinter> \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; ((\<tau> q1 \<parallel> \<tau> q2) \<squnion> ((\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m) \<parallel> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (simp add: par_distrib_finite_if_idempotent_helper par.sync_commute)
      also have "... = (a ; (a \<^sup>;^ i)) \<iinter> \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; ((\<tau> q1 \<parallel> \<tau> q2) \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (simp add: par_distrib_finite_if_idempotent_helper_2)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; ((a ; (a \<^sup>;^ i)) \<iinter> ((\<tau> q1 \<parallel> \<tau> q2) \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        by (simp add: assert_seq_assert conj.assert_command_sync_command)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (a ; (a \<^sup>;^ i) \<iinter> (\<tau> q1 \<parallel> \<tau> q2) \<squnion> (a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        by (simp add: conj.sync_nondet_distrib)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (a ; (a \<^sup>;^ i) \<iinter> \<tau> (q1 \<sqinter> q2) \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a \<^sup>;^ Suc i) \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        by (metis par.test_sync_to_inf dist1)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (\<bottom> \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a \<^sup>;^ Suc i) \<iinter> ((atomic (b1\<^sub>m)) ; c1\<^sub>m \<parallel> (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        using a_def conj_commute conj.sync_commute atomic_test by presburger
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (a ; (a \<^sup>;^ i)) \<iinter> ((atomic (b1\<^sub>m) \<parallel> atomic (b2\<^sub>m)) ; (c1\<^sub>m \<parallel> c2\<^sub>m))))"
        by (simp add: par.atomic_pre_sync_atomic_pre)
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. ((a \<^sup>;^ Suc i) \<iinter> atomic (b1\<^sub>m) ; c1\<^sub>m) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> atomic (b2\<^sub>m) ; c2\<^sub>m)))"
        using par_distrib_finite_if_idempotent_helper_5 a_idem induction_hyps by auto
      also have "... = \<lbrace>p1\<rbrace> ; \<lbrace>p2\<rbrace> ; (((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m)))"
        using par_distrib_finite_if_idempotent_helper_7 a_def by auto
      also have "... = ((\<lbrace>p1\<rbrace> ; ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)))) \<parallel> ((\<lbrace>p2\<rbrace> ; ((a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        by (smt (verit) par.assert_distrib par_commute seq_assoc)
      also have "... = ((\<lbrace>p1\<rbrace> ; (\<bottom> \<squnion> (a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)))) \<parallel> ((\<lbrace>p2\<rbrace> ; (\<bottom> \<squnion> (a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        by auto
      also have "... = ((\<lbrace>p1\<rbrace> ; ((a \<^sup>;^ Suc i) \<iinter> \<tau> q1 \<squnion> (a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)))) \<parallel> ((\<lbrace>p2\<rbrace> ; ((a \<^sup>;^ Suc i) \<iinter> \<tau> q2 \<squnion> (a \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        using ai_conj_q1 ai_conj_q2 by auto
      also have "... = ((\<lbrace>p1\<rbrace> ; (a \<^sup>;^ Suc i) \<iinter> (\<tau> q1 \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)))) \<parallel> ((\<lbrace>p2\<rbrace> ; (a \<^sup>;^ Suc i) \<iinter> (\<tau> q2 \<squnion> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        by (smt (verit, ccfv_threshold) conj.assert_distrib conj.nondet_sync_distrib local.conj_commute)
      also have "... = ((a \<^sup>;^ Suc i) \<iinter> (\<lbrace>p1\<rbrace> ; (\<tau> q1 \<squnion> (\<Squnion>(b1\<^sub>m, c1\<^sub>m)\<in>M1. (atomic (b1\<^sub>m)) ; c1\<^sub>m)))) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> (\<lbrace>p2\<rbrace> ; (\<tau> q2 \<squnion> (\<Squnion>(b2\<^sub>m, c2\<^sub>m)\<in>M2. (atomic (b2\<^sub>m)) ; c2\<^sub>m))))"
        by (smt (verit) conj.assert_distrib local.conj_commute)
      also have "... = ((a \<^sup>;^ Suc i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ Suc i) \<iinter> c\<^sub>2)"
        using c1_expanded c2_expanded by fastforce
      finally show ?thesis .
    qed
  }
  then show ?case
    by simp
qed

lemma par_distrib_finite_if_idempotent:
  assumes a_def [simp]: "a = atomic(g, r)" 
  assumes a_idem: "a = a \<parallel> a"
  shows "(a \<^sup>;^ i) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) = ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2)"
  using par_distrib_finite_if_idempotent_forall a_def a_idem by blast

lemma par_distrib_infinite_if_idempotent:
  assumes a_def [simp]: "a = atomic(g, r)"
  assumes a_idem: "a \<parallel> a = a"
  shows "a\<^sup>\<infinity> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) = (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)"
proof (rule antisym)
  have a1: "a\<^sup>\<infinity> = (a \<parallel> a)\<^sup>\<infinity>"
    by (metis a_idem)
  have a2: "a\<^sup>\<infinity> = a\<^sup>\<infinity> \<parallel> a\<^sup>\<infinity>"
    by (metis a1 par.atomic_infiter_sync a_def)
  have "a\<^sup>\<infinity> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) = (a\<^sup>\<infinity> \<parallel> a\<^sup>\<infinity>) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)"
    by (metis a2)
  also have "... \<ge> (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)"
    by (metis par_conj_interchange)
  finally show "a\<^sup>\<infinity> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) \<ge> (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)" .
next
  show "a\<^sup>\<infinity> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) \<le> (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)"
    sorry
qed

lemma conj_par_link_finite: "(\<alpha>(r) \<^sup>;^ i) \<iinter> c = (\<epsilon>(r) \<^sup>;^ i) \<parallel> c"
proof (rule antisym)
  have r_par_Atomic: "\<alpha>(r) = \<alpha>(r) \<parallel> Atomic"
    by (smt (verit, ccfv_threshold) Atomic2_def Atomic_def2 Env_def Pgm_def env_par_env_axiom env_par_pgm_axiom flip_def2 general_atomic.Hom_ref_hom general_atomic_def inf.orderI inf_absorb1 inf_top_left par.sync_nondet_distrib par_assoc par_atomic_idempotent pgm_env_inf_nondet)
  have r_conj_env: "(\<alpha>(r) \<^sup>;^ i) \<iinter> \<E>\<^sup>\<omega> = \<epsilon>(r) \<^sup>;^ i"
  proof -
    have r_conj_env_atomic: "\<alpha>(r) \<iinter> \<E> = \<epsilon>(r)"
      by (simp add: Env_def conj.sync_nondet_distrib env_conj_env env_conj_pgm general_atomic_def local.conj_commute)
    show ?thesis
      using conj.omega_sync_finite conj_commute r_conj_env_atomic
      by (metis atomic_general_atomic par.syncid_atomic)
  qed

  have "(\<alpha>(r) \<^sup>;^ i) \<iinter> c = ((\<alpha>(r) \<parallel> Atomic) \<^sup>;^ i) \<iinter> (c \<parallel> \<E>\<^sup>\<omega>)"
    using r_par_Atomic par_identity Atomic_def by auto
  also have "... = ((\<alpha>(r) \<^sup>;^ i) \<parallel> Atomic\<^sup>\<omega>) \<iinter> (c \<parallel> \<E>\<^sup>\<omega>)"
    by (metis Atomic_def general_atomic_def par.omega_sync_finite par_commute pgm_or_env_atomic)
  also have "... \<ge> (Atomic\<^sup>\<omega> \<iinter> c) \<parallel> ((\<alpha>(r) \<^sup>;^ i) \<iinter> \<E>\<^sup>\<omega>)"
    by (simp add: par_conj_interchange par_commute)
  finally show "(\<alpha>(r) \<^sup>;^ i) \<iinter> c \<ge> (\<epsilon>(r) \<^sup>;^ i) \<parallel> c"
    by (metis conj_id local.conj_commute par_commute r_conj_env)
next
  have omega_ref_i: "\<alpha>(r)\<^sup>\<omega> \<ge> (\<alpha>(r) \<^sup>;^ i)"
    by (simp add: iter_i)
  have r_conj_env: "(\<alpha>(r) \<^sup>;^ i) \<iinter> \<E>\<^sup>\<omega> = \<epsilon>(r) \<^sup>;^ i"
  proof -
    have r_conj_env_atomic: "\<alpha>(r) \<iinter> \<E> = \<epsilon>(r)"
      by (simp add: Env_def conj.sync_nondet_distrib env_conj_env env_conj_pgm general_atomic_def local.conj_commute)
    show ?thesis
      using conj.omega_sync_finite conj_commute r_conj_env_atomic
      by (metis atomic_general_atomic par.syncid_atomic)
  qed
  have c_conj_ref: "c \<ge> (\<alpha>(r) \<^sup>;^ i) \<iinter> c"
  proof -
    have "c \<ge> \<alpha>(r)\<^sup>\<omega> \<iinter> c"
      by (metis atomic_general_atomic atomic_iter_intro)
    then show ?thesis
      by (smt (verit) conj.nondet_sync_distrib4 local.conj_commute omega_ref_i sup.absorb_iff1 sup.absorb_iff2)
  qed
  have par_idem: "\<alpha>(r) = \<alpha>(r) \<parallel> \<alpha>(r)"
    by (simp add: general_atomic_def par_atomic_idempotent)

  have a1: "(\<epsilon>(r) \<^sup>;^ i) \<parallel> c \<ge> ((\<alpha>(r) \<^sup>;^ i) \<iinter> \<E>\<^sup>\<omega>) \<parallel> ((\<alpha>(r) \<^sup>;^ i) \<iinter> c)"
    by (simp add: c_conj_ref par.sync_mono_right r_conj_env)
  have a2: "(\<epsilon>(r) \<^sup>;^ i) \<parallel> c \<ge> (\<alpha>(r) \<^sup>;^ i) \<iinter> (\<E>\<^sup>\<omega> \<parallel> c)"
    using a1 par_idem par_distrib_finite_if_idempotent atomic_def general_atomic_def by fastforce
  show "(\<epsilon>(r) \<^sup>;^ i) \<parallel> c \<ge> (\<alpha>(r) \<^sup>;^ i) \<iinter> c"
    using a2 par_skip_left skip_def by auto
qed

lemma conj_par_link_infinite: "\<alpha>(r)\<^sup>\<infinity> \<iinter> c = \<epsilon>(r)\<^sup>\<infinity> \<parallel> c"
proof (rule antisym)
  have r_par_Atomic: "\<alpha>(r) = \<alpha>(r) \<parallel> Atomic"
    by (smt (verit, ccfv_threshold) Atomic2_def Atomic_def2 Env_def Pgm_def env_par_env_axiom env_par_pgm_axiom flip_def2 general_atomic.Hom_ref_hom general_atomic_def inf.orderI inf_absorb1 inf_top_left par.sync_nondet_distrib par_assoc par_atomic_idempotent pgm_env_inf_nondet)
  have r_conj_env: "\<alpha>(r)\<^sup>\<infinity> \<iinter> \<E>\<^sup>\<omega> = \<epsilon>(r)\<^sup>\<infinity>"
  proof -
    have "\<alpha>(r)\<^sup>\<infinity> \<iinter> \<E>\<^sup>\<omega> = \<alpha>(r)\<^sup>\<infinity> \<iinter> \<E>\<^sup>\<infinity>"
      by (simp add: conj.inf_subsumes local.conj_commute)
    also have "... = (\<alpha>(r) \<iinter> \<E>)\<^sup>\<infinity>"
      by (metis conj.atomic_infiter_sync general_atomic_def par.syncid_atomic pgm_or_env_atomic)
    finally show ?thesis
      by (metis Atomic_def2 Env_def Pgm_def conj.sync_nondet_distrib env_atomic env_conj_pgm general_atomic_def local.conj_commute par.conj_atomic_sync_identity)
  qed

  have "\<alpha>(r)\<^sup>\<infinity> \<iinter> c = ((\<alpha>(r) \<parallel> Atomic)\<^sup>\<infinity>) \<iinter> (c \<parallel> \<E>\<^sup>\<omega>)"
    using r_par_Atomic par_identity Atomic_def by auto
  also have "... = (\<alpha>(r)\<^sup>\<infinity> \<parallel> Atomic\<^sup>\<omega>) \<iinter> (c \<parallel> \<E>\<^sup>\<omega>)"
    by (metis Atomic_def general_atomic_def par.inf_subsumes par.atomic_infiter_sync par_commute pgm_or_env_atomic)
  also have "... \<ge> (Atomic\<^sup>\<omega> \<iinter> c) \<parallel> (\<alpha>(r)\<^sup>\<infinity> \<iinter> \<E>\<^sup>\<omega>)"
    by (metis par_commute par_conj_interchange)
  finally show "\<alpha>(r)\<^sup>\<infinity> \<iinter> c \<ge> \<epsilon>(r)\<^sup>\<infinity> \<parallel> c"
    by (metis conj_id local.conj_commute par_commute r_conj_env)
next
  have omega_ref_i: "\<alpha>(r)\<^sup>\<omega> \<ge> \<alpha>(r)\<^sup>\<infinity>"
    by (simp add: iter_ref_infiter)
  have r_conj_env: "\<alpha>(r)\<^sup>\<infinity> \<iinter> \<E>\<^sup>\<omega> = \<epsilon>(r)\<^sup>\<infinity>"
  proof -
    have "\<alpha>(r)\<^sup>\<infinity> \<iinter> \<E>\<^sup>\<omega> = \<alpha>(r)\<^sup>\<infinity> \<iinter> \<E>\<^sup>\<infinity>"
      by (simp add: conj.inf_subsumes local.conj_commute)
    also have "... = (\<alpha>(r) \<iinter> \<E>)\<^sup>\<infinity>"
      by (metis conj.atomic_infiter_sync general_atomic_def par.syncid_atomic pgm_or_env_atomic)
    finally show ?thesis
      by (metis Atomic_def2 Env_def Pgm_def conj.sync_nondet_distrib env_atomic env_conj_pgm general_atomic_def local.conj_commute par.conj_atomic_sync_identity)
  qed
  have c_conj_ref: "c \<ge> \<alpha>(r)\<^sup>\<infinity> \<iinter> c"
  proof -
    have "c \<ge> \<alpha>(r)\<^sup>\<omega> \<iinter> c"
      by (metis atomic_general_atomic atomic_iter_intro)
    then show ?thesis
      by (smt (verit) conj.nondet_sync_distrib4 local.conj_commute omega_ref_i sup.absorb_iff1 sup.absorb_iff2)
  qed
  have par_idem: "\<alpha>(r) = \<alpha>(r) \<parallel> \<alpha>(r)"
    by (simp add: general_atomic_def par_atomic_idempotent)

  have a1: "\<epsilon>(r)\<^sup>\<infinity> \<parallel> c \<ge> (\<alpha>(r)\<^sup>\<infinity> \<iinter> \<E>\<^sup>\<omega>) \<parallel> (\<alpha>(r)\<^sup>\<infinity> \<iinter> c)"
    by (simp add: c_conj_ref par.sync_mono_right r_conj_env)
  have a2: "\<epsilon>(r)\<^sup>\<infinity> \<parallel> c \<ge> \<alpha>(r)\<^sup>\<infinity> \<iinter> (\<E>\<^sup>\<omega> \<parallel> c)"
    using a1 par_idem par_distrib_infinite_if_idempotent atomic_def general_atomic_def by fastforce
  show "\<epsilon>(r)\<^sup>\<infinity> \<parallel> c \<ge> \<alpha>(r)\<^sup>\<infinity> \<iinter> c"
    using a2 par_skip_left skip_def by auto
qed

lemma extract_iter_count_finite: "((\<alpha>(r) \<^sup>;^ i) \<iinter> c) \<parallel> d = (\<alpha>(r) \<^sup>;^ i) \<iinter> (c \<parallel> d)"
proof -
  have "((\<alpha>(r) \<^sup>;^ i) \<iinter> c) \<parallel> d = ((\<epsilon>(r) \<^sup>;^ i) \<parallel> c) \<parallel> d"
    by (metis conj_par_link_finite)
  also have "... = (\<epsilon>(r) \<^sup>;^ i) \<parallel> (c \<parallel> d)"
    by (metis par_assoc)
  also have "... = (\<alpha>(r) \<^sup>;^ i) \<iinter> (c \<parallel> d)"
    by (metis conj_par_link_finite)
  finally show ?thesis .
qed

lemma extract_iter_count_infinite: "(\<alpha>(r)\<^sup>\<infinity> \<iinter> c) \<parallel> d = \<alpha>(r)\<^sup>\<infinity> \<iinter> (c \<parallel> d)" 
proof -
  have "(\<alpha>(r)\<^sup>\<infinity> \<iinter> c) \<parallel> d = (\<epsilon>(r)\<^sup>\<infinity> \<parallel> c) \<parallel> d"
    by (metis conj_par_link_infinite)
  also have "... = \<epsilon>(r)\<^sup>\<infinity> \<parallel> (c \<parallel> d)"
    by (metis par_assoc)
  also have "... = \<alpha>(r)\<^sup>\<infinity> \<iinter> (c \<parallel> d)"
    by (metis conj_par_link_infinite)
  finally show ?thesis .
qed 

lemma par_atomic_iter_absorb_helper:
  assumes "i > 0"
  assumes "a = atomic(g, r)"
  shows "(Atomic \<^sup>;^ j) \<iinter> (a \<^sup>;^ j) ; (a \<^sup>;^ i) = (a \<^sup>;^ j) ; \<bottom>"
proof (induct j)
  case 0
  have "(Atomic \<^sup>;^ 0) \<iinter> (a \<^sup>;^ 0) ; (a \<^sup>;^ i) = nil \<iinter> (a \<^sup>;^ i)"
    by simp
  also have "... = \<tau> \<top> \<iinter> a ; (a \<^sup>;^ (i-1))"
    by (metis Suc_pred' assms(1) seq_power_Suc test_top)
  also have "... = \<bottom>"
    by (metis conj.test_sync_atomic_pre assms(2))
  also have "... = (a \<^sup>;^ 0) ; \<bottom>"
    by simp
  finally show ?case .
next
  case (Suc j)
  have "(Atomic \<^sup>;^ (Suc j)) \<iinter> (a \<^sup>;^ (Suc j)) ; (a \<^sup>;^ i) = (Atomic ; (Atomic \<^sup>;^ j)) \<iinter> (a ; (a \<^sup>;^ j)) ; (a \<^sup>;^ i)"
    by simp
  also have "... = (Atomic \<iinter> a) ; ((Atomic \<^sup>;^ j) \<iinter> (a \<^sup>;^ j) ; (a \<^sup>;^ i))"
    by (metis Atomic_def assms(2) conj.atomic_pre_sync_atomic_pre seq_assoc)
  also have "... = (Atomic \<iinter> a) ; (a \<^sup>;^ j) ; \<bottom>"
    by (metis Suc.hyps seq_assoc)
  also have "... = (a ; (a \<^sup>;^ j)) ; \<bottom>"
    by (simp add: assms(2) par.conj_atomic_sync_identity)
  finally show ?case
    by simp
qed

lemma par_atomic_iter_absorb_finite:
  assumes "j < k"
  assumes "a = atomic(g, r)"
  shows "((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2) \<le> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>2)"
proof -
  have aj_conj_Atomic_j: "a \<^sup>;^ j = (Atomic \<^sup>;^ j) \<iinter> (a \<^sup>;^ j)"
    by (metis Atomic_conj_atomic_finite assms(2))
  have ak_expanded: "(a \<^sup>;^ k) = (a \<^sup>;^ j) ; (a \<^sup>;^ (k - j))"
    by (metis assms(1) seq_power_split_less)
  have k_minus_j: "k - j > 0"
    by (simp add: assms(1))
  have a1: "(Atomic \<^sup>;^ j) \<iinter> (a \<^sup>;^ j) ; (a \<^sup>;^ (k - j)) = (a \<^sup>;^ j) ; \<bottom>"
    by (metis par_atomic_iter_absorb_helper k_minus_j assms(2))

  have "((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2) = ((Atomic \<^sup>;^ j) \<iinter> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)) \<parallel> ((a \<^sup>;^ j) ; (a \<^sup>;^ (k - j)) \<iinter> c\<^sub>2)"
    by (metis aj_conj_Atomic_j ak_expanded conj_assoc)
  also have "... = ((\<alpha>(\<top>) \<^sup>;^ j) \<iinter> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)) \<parallel> ((a \<^sup>;^ j) ; (a \<^sup>;^ (k - j)) \<iinter> c\<^sub>2)"
    by (simp add: Atomic_def2 Env_def Pgm_def general_atomic_def)
  also have "... = (\<alpha>(\<top>) \<^sup>;^ j) \<iinter> (((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ j) ; (a \<^sup>;^ (k - j)) \<iinter> c\<^sub>2))"
    by (metis extract_iter_count_finite)
  also have "... = (\<alpha>(\<top>) \<^sup>;^ j) \<iinter> (((a \<^sup>;^ j) ; (a \<^sup>;^ (k - j)) \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1))"
    by (metis par_commute)
  also have "... = ((\<alpha>(\<top>) \<^sup>;^ j) \<iinter> (a \<^sup>;^ j) ; (a \<^sup>;^ (k - j)) \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)"
    by (metis extract_iter_count_finite conj_assoc)
  also have "... = ((Atomic \<^sup>;^ j) \<iinter> (a \<^sup>;^ j) ; (a \<^sup>;^ (k - j)) \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)"
    by (simp add: Atomic_def2 Env_def Pgm_def general_atomic_def)
  also have "... = ((a \<^sup>;^ j) ; \<bottom> \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)"
    by (simp add: a1)
  also have "... \<le> ((a \<^sup>;^ j) ; nil \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)"
    by (metis conj.sync_mono_left iter1 nil_iter par.sync_mono_left seq_mono_right)
  also have "... \<le> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>2)"
    by (simp add: par_commute)
  finally show ?thesis .
qed

lemma par_atomic_iter_absorb_infinite:
  assumes "a = atomic(g, r)"
  shows "((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<le> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>2)"
proof -
  have aj_conj_Atomic_j: "a \<^sup>;^ j = (Atomic \<^sup>;^ j) \<iinter> (a \<^sup>;^ j)"
    by (metis Atomic_conj_atomic_finite assms)
  have ak_expanded: "a\<^sup>\<infinity> = (a \<^sup>;^ j) ; a\<^sup>\<infinity>"
    by (simp add: infiter_unfold_any)
  have a1: "(Atomic \<^sup>;^ j) \<iinter> (a \<^sup>;^ j) ; a\<^sup>\<infinity> = (a \<^sup>;^ j) ; \<bottom>"
    by (metis (no_types, lifting) assms conj.atomic_infiter_sync_nil conj.atomic_power_pre_sync_power_pre inf.syncid_atomic local.conj_commute par.conj_atomic_sync_identity seq_nil_right)

  have "((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2) = ((Atomic \<^sup>;^ j) \<iinter> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)) \<parallel> ((a \<^sup>;^ j) ; a\<^sup>\<infinity> \<iinter> c\<^sub>2)"
    by (metis aj_conj_Atomic_j ak_expanded conj_assoc)
  also have "... = ((\<alpha>(\<top>) \<^sup>;^ j) \<iinter> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)) \<parallel> ((a \<^sup>;^ j) ; a\<^sup>\<infinity> \<iinter> c\<^sub>2)"
    by (simp add: Atomic_def2 Env_def Pgm_def general_atomic_def)
  also have "... = (\<alpha>(\<top>) \<^sup>;^ j) \<iinter> (((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ j) ; a\<^sup>\<infinity> \<iinter> c\<^sub>2))"
    by (metis extract_iter_count_finite)
  also have "... = (\<alpha>(\<top>) \<^sup>;^ j) \<iinter> (((a \<^sup>;^ j) ; a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1))"
    by (metis par_commute)
  also have "... = ((\<alpha>(\<top>) \<^sup>;^ j) \<iinter> (a \<^sup>;^ j) ; a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)"
    by (metis extract_iter_count_finite conj_assoc)
  also have "... = ((Atomic \<^sup>;^ j) \<iinter> (a \<^sup>;^ j) ; a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)"
    by (simp add: Atomic_def2 Env_def Pgm_def general_atomic_def)
  also have "... = ((a \<^sup>;^ j) ; \<bottom> \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)"
    by (simp add: a1)
  also have "... \<le> ((a \<^sup>;^ j) ; nil \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>1)"
    by (metis conj.sync_mono_left iter1 nil_iter par.sync_mono_left seq_mono_right)
  also have "... \<le> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>2)"
    by (simp add: par_commute)
  finally show ?thesis .
qed

lemma par_distrib_if_idempotent_helper:
  assumes atomic_a: "a = atomic(g, r)"
  assumes a_idem: "a = a \<parallel> a"
  shows "(\<Squnion>j::nat. (\<Squnion>k::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2))) = (\<Squnion>i::nat. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2))"
proof (rule antisym)
  show "(\<Squnion>j::nat. (\<Squnion>k::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2))) \<ge> (\<Squnion>i::nat. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2))"
    by (smt (z3) SUP_least Sup_upper image_eqI inf_sup_ord(3) order_trans)
next
  {
    fix j
    fix k
    have "\<exists>i. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2) \<ge> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2)"
    proof -
      define i where i_def: "i = min j k"
      have i_satisfies: "((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2) \<ge> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2)"
      proof (cases "j = k")
        case True
        show ?thesis
          using True i_def by auto
      next
        case False
        have j_ne_k: "j \<noteq> k" (* Rename the fact False so that it can used within another cases *)
          using False by auto
        show ?thesis
        proof (cases "j < k")
          case True
          have i_eq_j: "i = j"
            using True i_def by auto
          show ?thesis
            by (metis atomic_a i_eq_j True par_atomic_iter_absorb_finite)
        next
          case False
          have k_less_j: "k < j"
            using False j_ne_k nat_neq_iff by blast
          have i_eq_k: "i = k"
            using False i_def by auto
          show ?thesis
            by (metis atomic_a i_eq_k k_less_j par_atomic_iter_absorb_finite par_commute)
        qed
      qed
      show ?thesis
        using i_satisfies by auto
    qed
  }
  then have forall_jk_exists_i: "\<forall>j k. \<exists> i. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2) \<ge> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2)"
    by simp
  show "(\<Squnion>i::nat. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2)) \<ge> (\<Squnion>j::nat. (\<Squnion>k::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2)))"
    by (meson SUP_least SUP_upper2 UNIV_I forall_jk_exists_i)
qed

lemma par_distrib_if_idempotent_helper_2:
  assumes atomic_a: "a = atomic(g, r)"
  assumes a_idem: "a = a \<parallel> a"
  shows "(\<Squnion>i::nat. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)) \<le> (\<Squnion>i::nat. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2))"
  by (simp add: SUP_mono' atomic_a par_atomic_iter_absorb_infinite)

lemma par_distrib_if_idempotent:
  assumes atomic_a: "a = atomic(g, r)"
  assumes a_idem: "a = a \<parallel> a"
  shows "(a\<^sup>\<omega> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<omega> \<iinter> c\<^sub>2) = a\<^sup>\<omega> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)"
proof -
  have a_iter_expanded: "a\<^sup>\<omega> = ((\<Squnion>i::nat. a \<^sup>;^ i) \<squnion> a\<^sup>\<infinity>)"
    by (simp add: chaos_def par.fiter_seq_choice par.iter_isolation)

  define f where f_def: "f \<equiv> \<lambda> j. a \<^sup>;^ j"
  define g where g_def: "g \<equiv> \<lambda> j. f(j) \<iinter> c\<^sub>1" 
  
  have dist1: "(\<Squnion>j::nat. f(j)) \<iinter> c\<^sub>1 = (\<Squnion>j::nat. f(j) \<iinter> c\<^sub>1)"
    by (metis conj.NONDET_sync_distrib empty_not_UNIV local.conj_commute)
  have dist2: "((\<Squnion>k::nat. a \<^sup>;^ k) \<squnion> a\<^sup>\<infinity>) \<iinter> c\<^sub>2 = (\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>2"
    by (metis UNIV_not_empty conj.NONDET_sync_distrib conj.sync_nondet_distrib f_def local.conj_commute)

  have refine1: "(\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<le> (\<Squnion>k::nat. ((a \<^sup>;^ k) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2))"
  proof -
    have "(\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1) = (\<Squnion>k::nat. ((a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1))"
      by (simp add: par.NONDET_sync_distrib)
    also have "... \<le> (\<Squnion>k::nat. ((a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>1))"
      using atomic_a a_idem par_distrib_if_idempotent_helper_2 by auto
    finally show ?thesis
      by (simp add: par_commute)
  qed 
  have refine2: "(\<Squnion>j::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)) \<le> (\<Squnion>j::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ j) \<iinter> c\<^sub>2))"
    using atomic_a a_idem par_distrib_if_idempotent_helper_2 by auto
  
  have "(a\<^sup>\<omega> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<omega> \<iinter> c\<^sub>2) = (a\<^sup>\<omega> \<iinter> c\<^sub>2) \<parallel> (((\<Squnion>j::nat. a \<^sup>;^ j) \<squnion> (a\<^sup>\<infinity>)) \<iinter> c\<^sub>1)"
    by (metis a_iter_expanded par_commute)
  also have "... = (a\<^sup>\<omega> \<iinter> c\<^sub>2) \<parallel> ((\<Squnion>j::nat. a \<^sup>;^ j) \<iinter> c\<^sub>1 \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    using conj.nondet_sync_distrib by fastforce
  also have "... = (a\<^sup>\<omega> \<iinter> c\<^sub>2) \<parallel> ((\<Squnion>j::nat. f(j)) \<iinter> c\<^sub>1 \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (simp add: f_def)
  also have "... = (a\<^sup>\<omega> \<iinter> c\<^sub>2) \<parallel> ((\<Squnion>j::nat. f(j) \<iinter> c\<^sub>1) \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (metis dist1)
  also have "... = (a\<^sup>\<omega> \<iinter> c\<^sub>2) \<parallel> (\<Squnion>j::nat. g(j)) \<squnion> (a\<^sup>\<omega> \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (simp add: par.sync_nondet_distrib g_def)
  also have "... = (\<Squnion>j::nat. (a\<^sup>\<omega> \<iinter> c\<^sub>2) \<parallel> g(j)) \<squnion> (a\<^sup>\<omega> \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (simp add: image_image par.sync_Nondet_distrib)
  also have "... = (\<Squnion>j::nat. (((\<Squnion>k::nat. a \<^sup>;^ k) \<squnion> a\<^sup>\<infinity>) \<iinter> c\<^sub>2) \<parallel> g(j)) \<squnion> (((\<Squnion>k::nat. a \<^sup>;^ k) \<squnion> a\<^sup>\<infinity>) \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (simp add: a_iter_expanded)
  also have "... = (\<Squnion>j::nat. ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> g(j)) \<squnion> ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (metis dist2)
  also have "... = (\<Squnion>j::nat. (\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> g(j) \<squnion> (a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> g(j)) \<squnion> ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (simp add: par.nondet_sync_distrib)
  also have "... = (\<Squnion>j::nat. (\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2 \<parallel> g(j)) \<squnion> (a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> g(j)) \<squnion> ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (simp add: par.NONDET_sync_distrib)
  also have "... = (\<Squnion>j::nat. (\<Squnion>k::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2)) \<squnion> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)) \<squnion> ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<squnion> a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)"
    by (simp add: f_def g_def par_commute)
  also have "... = (\<Squnion>j::nat. (\<Squnion>k::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2)) \<squnion> ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)) \<squnion> ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)) \<squnion> (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)"
    by (simp add: par.nondet_sync_distrib4 par_commute sup_commute)
  also have "... = (\<Squnion>j::nat. (\<Squnion>k::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2))) \<squnion> (\<Squnion>j::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)) \<squnion> ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1)) \<squnion> (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)"
    by (simp add: complete_lattice_class.SUP_sup_distrib)
  also have "... = (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<squnion> (\<Squnion>j::nat. (\<Squnion>k::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ k) \<iinter> c\<^sub>2))) \<squnion> (\<Squnion>j::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)) \<squnion> ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1))"
    by (simp add: inf_sup_aci(5) sup_left_commute)
  also have "... = (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<squnion> (\<Squnion>i::nat. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2)) \<squnion> (\<Squnion>j::nat. ((a \<^sup>;^ j) \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2)) \<squnion> ((\<Squnion>k::nat. (a \<^sup>;^ k) \<iinter> c\<^sub>2) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>1))"
    using par_distrib_if_idempotent_helper atomic_a a_idem by auto
  also have "... = (a\<^sup>\<infinity> \<iinter> c\<^sub>1) \<parallel> (a\<^sup>\<infinity> \<iinter> c\<^sub>2) \<squnion> (\<Squnion>i::nat. ((a \<^sup>;^ i) \<iinter> c\<^sub>1) \<parallel> ((a \<^sup>;^ i) \<iinter> c\<^sub>2))"
    by (smt (verit, ccfv_threshold) refine1 refine2 inf_sup_aci(5) le_iff_sup sup.left_commute)
  also have "... = a\<^sup>\<infinity> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) \<squnion> (\<Squnion>i::nat. ((a \<^sup>;^ i) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)))"
    using par_distrib_infinite_if_idempotent atomic_a a_idem par_distrib_finite_if_idempotent by auto
  also have "... = a\<^sup>\<infinity> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) \<squnion> (\<Squnion>i::nat. f(i) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2))"
    using f_def by auto
  also have "... = a\<^sup>\<infinity> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) \<squnion> (\<Squnion>i::nat. f(i)) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)"
    by (simp add: conj.NONDET_sync_distrib)
  also have "... = a\<^sup>\<infinity> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2) \<squnion> (\<Squnion>i::nat. a \<^sup>;^ i) \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)"
    by (metis f_def)
  also have "... = a\<^sup>\<omega> \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)"
    by (simp add: a_iter_expanded conj.sync_nondet_distrib inf_sup_aci(5) local.conj_commute)
  finally show ?thesis . 
qed

end

end