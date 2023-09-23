theory CouplingInvariants (* OBSOLETE - See Invariants.thy *)
  imports DataRefinement
begin                                   
                       
locale coupling_inv = data_refines 
begin                  

lemma iter_conj_conj_distrib_left: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>"
  oops  
 (* by (simp add: iter0 iter_conj_distrib) *)

lemma iter_conj_par_distrib: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c \<iinter> d)\<^sup>\<omega>"
  oops
(*proof -
  have a: "c\<^sup>\<omega> \<ge> c" by (metis iter1)
  have b: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>" by (metis iter_conj_conj_distrib_left)
  have "c\<^sup>\<omega> \<iinter> d \<ge> c \<iinter> d" using a 
    by (simp add: conj.sync_mono_left)
  thus ?thesis using a b by (metis refine_trans iter_mono) 
qed
*)

notation conj (infixl "\<oplus>" 40) 

lemma iter_seq_split: "((iter a) \<oplus> (c ; d)) =
       ((iter a \<oplus> (((c \<oplus> fiter Atomic) ; d))) \<squnion> (iter a \<oplus> ((c \<oplus> infiter Atomic)) ; d))"
  apply (subst conj_chaos[where a=c, symmetric])
  using chaos_def conj.sync_nondet_distrib nondet_seq_distrib par.iter_isolation by presburger

lemma conj_inf_abort: "(c \<oplus> infiter s) = (c \<oplus> infiter s) ; top"
  by (metis assert_bot conj.test_sync_post_helper1 infiter_iter_magic test.hom_bot)

lemma conj_inf_annihilate:
"(c \<oplus> infiter s) ; d = (c \<oplus> infiter s)"
  by (metis conj_inf_abort seq_abort seq_assoc)

lemma "a = atomic s \<Longrightarrow> (iter a \<oplus> ((c \<oplus> infiter Atomic) ; d)) = (infiter a \<oplus> c) ;  (iter a \<oplus> d) "
  apply (subst conj_inf_annihilate)
  by (metis (no_types, lifting) conj.comm.left_commute conj.test_sync_post
                conj_id conj_inf_annihilate infiter_iter_magic test.hom_bot)

declare guar_def[simp del]
declare rely_def[simp del]
declare dem_def[simp del]

declare [[show_types=false]][[show_sorts=false]]


lemma inf_helper: "(\<Sqinter> M \<oplus> a) \<le> (\<Sqinter> ((conj a) ` M))"
  apply (subst le_Inf_iff, clarsimp)
  by (metis Inf_lower conj.sync_mono_right local.conj_commute)

lemma gfp_ordinal_induct_top:
  fixes f :: "'x::complete_lattice \<Rightarrow> 'x"
  assumes mono: "mono f"
    and P_f: "\<And>S. P S \<Longrightarrow> gfp f \<le> S \<Longrightarrow> P (f S)"
    and P_Union: "\<And>M. M \<noteq> {} \<Longrightarrow> \<forall>S\<in>M. P S \<Longrightarrow> P (Inf M)"
    and P_top: "{S. gfp f \<le> S \<and> P S} \<noteq> {}"
  shows "P (gfp f)"
proof -
  let ?M = "{S. gfp f \<le> S \<and> P S}"
  from P_Union have "P (Inf ?M)" 
    apply (case_tac "{S. gfp f \<le> S \<and> P S} = {}")
    using P_top apply auto[1]
    apply (clarsimp)
    done
  also have "Inf ?M = gfp f"
  proof (rule antisym)
    show "gfp f \<le> Inf ?M"
      by (blast intro: Inf_greatest)
    then have "f (gfp f) \<le> f (Inf ?M)"
      by (rule mono [THEN monoD])
    then have "gfp f \<le> f (Inf ?M)"
      using mono [THEN gfp_unfold] by simp
    then have "f (Inf ?M) \<in> ?M"
      using P_Union 
      using P_f \<open>gfp f \<le> \<Sqinter> {S. gfp f \<le> S \<and> P S}\<close> calculation by blast
    then have "Inf ?M \<le> f (Inf ?M)"
      by (rule Inf_lower)
    then show "Inf ?M \<le> gfp f"
      by (rule gfp_upperbound)
  qed
  finally show ?thesis .
qed




lemma conj_bot_bot: "conj bot x = conj bot x ; y"
  by (metis antisym seq_abort seq_abort_conj seq_abort_right seq_assoc seq_magic_left)

end

end