section \<open>Termination\<close>

theory Termination
imports
  "ParallelFlip"
begin
  
locale term_op = parallel_flip (* lib_first
  for lib_first :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("F\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

definition terminate :: "'a::refinement_lattice" ("term")
  where "term = (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>" 

(* Exists only as a copy of terminate_def, with a shorter name. We cannot
   change the definition name from terminate to term because of reserved keyword issues. *)
lemmas term_def = terminate_def

lemma term_def2: "term = \<E>\<^sup>\<omega>;(Pgm;\<E>\<^sup>\<omega>)\<^sup>\<star>"
  using term_def sup_commute par.fiter_decomp_iter Env_def Env_def Pgm_def by metis

lemma term_def3: "term = \<epsilon>(\<top>)\<^sup>\<omega>;(\<pi>(\<top>);\<epsilon>(\<top>)\<^sup>\<omega>)\<^sup>\<star>"
  using term_def sup_commute par.fiter_decomp_iter by metis

lemma term_nonaborting: "chaos \<ge> term"
proof -
  have "(Pgm \<squnion> \<E>)\<^sup>\<omega> \<ge> \<E>\<^sup>\<omega>;(Pgm;\<E>\<^sup>\<omega>)\<^sup>\<star>"
    by (simp add: sup_commute par.iter_decomp iter_ref_fiter seq_mono)
  then show ?thesis using chaos_rel term_def2 by metis
qed

lemma seq_term_term: "term = term;term"
  using par.fiter_iter_seq term_def sup_commute by metis

lemma term_nil: "term \<ge> nil"
  unfolding term_def using iter0 fiter0 seq_mono by fastforce

lemma term_par_term_generic:
  shows "(\<pi>(r) \<squnion>  \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(r) \<squnion>  \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> = (\<pi>(r) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> "
proof -
  define a0 where "a0 \<equiv> \<pi>(r) \<squnion> \<epsilon>(\<top>)"
  define a1 where "a1 \<equiv> \<epsilon>(\<top>)"
  have a1: "(a0)\<^sup>\<star>;a1\<^sup>\<omega> \<parallel> a0\<^sup>\<star>;a1\<^sup>\<omega> =(a0\<parallel>a0)\<^sup>\<star>;(a1\<parallel>a0)\<^sup>\<star>;(a1\<parallel>a1)\<^sup>\<omega>"
    unfolding  a0_def a1_def using par.atomic_fiter_iter_sync_fiter_iter_symmetric 
        env_atomic pgm_or_env_atomic by metis
  moreover have "a0\<parallel>a0 = a0" using pgmenv_par_pgmenv a0_def by simp
  moreover have "a0\<parallel>a1 = a0" using pgmenv_par_env a0_def a1_def by simp
  moreover have "a1\<parallel>a1 = a1" unfolding a1_def by (simp add: env_par_env_axiom)
  ultimately have "(a0)\<^sup>\<star>;a1\<^sup>\<omega> \<parallel> a0\<^sup>\<star>;a1\<^sup>\<omega>  = (a0)\<^sup>\<star>;a1\<^sup>\<omega>"
    by (simp add: par_commute)
  then show ?thesis unfolding term_def a0_def a1_def by metis
qed

lemma par_term_term:
  shows "term \<parallel> term = term"
  using term_par_term_generic term_def by simp

lemma term_pseudo_atomic_fixed_point: "term = (\<alpha>(\<top>) \<squnion> \<alpha>(\<bottom>) ; \<top>) ; term \<squnion> nil"
proof -
  have term_def: "term = (\<alpha>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    by (simp add: general_atomic_def terminate_def)
  also have "... = (nil \<squnion> \<alpha>(\<top>) ; \<alpha>(\<top>)\<^sup>\<star>) ; \<epsilon>(\<top>)\<^sup>\<omega>"
    by (metis fiter_unfold)
  also have "... = \<epsilon>(\<top>)\<^sup>\<omega> \<squnion> \<alpha>(\<top>) ; \<alpha>(\<top>)\<^sup>\<star> ; \<epsilon>(\<top>)\<^sup>\<omega>"
    by (simp add: nondet_seq_distrib)
  also have "... = nil \<squnion> \<epsilon>(\<top>) ; \<epsilon>(\<top>)\<^sup>\<omega> \<squnion> \<alpha>(\<top>) ; \<alpha>(\<top>)\<^sup>\<star> ; \<epsilon>(\<top>)\<^sup>\<omega>"
    using iter_unfold by fastforce
  also have "... = nil \<squnion> \<alpha>(\<top>) ; \<alpha>(\<top>)\<^sup>\<star> ; \<epsilon>(\<top>)\<^sup>\<omega>"
    by (smt (verit, ccfv_threshold) fiter_unfold general_atomic_def inf_sup_aci(5) inf_sup_aci(6) nondet_seq_distrib par.seq_nondet_distrib seq_nil_right sup_idem)
  finally show ?thesis
    by (simp add: term_def seq_assoc sup_commute)
qed

lemma distrib_seq_par_term: "term \<parallel> (c ; d) = (term \<parallel> c) ; (term \<parallel> d)"
  using term_pseudo_atomic_fixed_point par.atomic_iter_distrib_seq
  by (metis Atomic_def Atomic_def2 Env_def Pgm_def atomic.hom_bot general_atomic.hom_bot general_atomic_def) 

lemma distrib_seq_conj_term: "term \<iinter> (c ; d) = (term \<iinter> c) ; (term \<iinter> d)"
  using term_pseudo_atomic_fixed_point conj.atomic_iter_distrib_seq
  by (metis Atomic_def Atomic_def2 Env_def Pgm_def atomic.hom_bot general_atomic.hom_bot general_atomic_def)

lemma pseudo_distrib_finite_iter_par_term: 
  assumes "c \<parallel> nil = \<bottom>"
  shows "term \<parallel> c\<^sup>\<star> = (term \<parallel> c)\<^sup>\<star>"
  by (metis Atomic_def Atomic_def2 Env_def Pgm_def atomic.hom_bot par.distrib_finite_iter2 general_atomic.hom_bot general_atomic_def term_pseudo_atomic_fixed_point)

lemma pseudo_distrib_finite_iter_conj_term: 
  assumes "c \<iinter> nil = \<bottom>"
  shows "term \<iinter> c\<^sup>\<star> = (term \<iinter> c)\<^sup>\<star>"
  by (metis Atomic_def Atomic_def2 Env_def Pgm_def atomic.hom_bot conj.distrib_finite_iter2 general_atomic.hom_bot general_atomic_def term_pseudo_atomic_fixed_point)

end
end