section \<open>Abstract view of atomic steps and tests with the weak conjunction operator\<close>

theory Abstract_Atomic_Sync_Test_With_Conj 
imports
  Abstract_Atomic_Sync_Test

begin

locale sync_command_aborting_with_conj = atomic_sync_command_with_tests_aborting + conjunction
  + conj: atomic_sync_command_with_tests_aborting seq test conj atomic chaos
  + assumes conj_atomic_sync_identity: "Atomic \<iinter> atomic p = atomic p" 
  assumes chaos_def: "chaos \<equiv> Atomic\<^sup>\<omega>" 

begin

(* Helper for atomic_iter_distrib_fixed_seq *)
lemma expanded_fixed_iter:
  assumes c_expanded: "c = \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; (c\<^sub>m)))"
  shows "(Atomic \<^sup>;^ Suc i) \<iinter> c = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m))"
proof (cases "M = {}")
  case False
  have M_nonempty: "M \<noteq> {}"
    by (simp add: False)

  define f where f_def: "f \<equiv> \<lambda> (b\<^sub>m, c\<^sub>m). atomic (b\<^sub>m) ; c\<^sub>m"
  have a2: "(Atomic \<^sup>;^ Suc i) \<iinter> (\<Squnion>m\<in>M. f(m)) = (\<Squnion>m\<in>M. (Atomic \<^sup>;^ Suc i) \<iinter> f(m))"
    by (metis conj.sync_NONDET_distrib M_nonempty)
  have a3: "(Atomic \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m))) = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (Atomic \<^sup>;^ Suc i) \<iinter> f((b\<^sub>m, c\<^sub>m)))"
    using a2 by fastforce

  have a1: "(Atomic \<^sup>;^ Suc i) \<iinter> \<tau> q = \<bottom>"
    by (simp add: Atomic_def conj.sync_commute conj.test_sync_atomic_pre)
  have "(Atomic \<^sup>;^ Suc i) \<iinter> c = (Atomic \<^sup>;^ Suc i) \<iinter> \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
    by (simp add: c_expanded)
  also have "... = \<lbrace>p\<rbrace> ; ((Atomic \<^sup>;^ Suc i) \<iinter> (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m)))"
    by (metis conj.assert_distrib)
  also have "... = \<lbrace>p\<rbrace> ; (Atomic ; (Atomic \<^sup>;^ i) \<iinter> \<tau> q \<squnion> (Atomic \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
    using conj.sync_nondet_distrib by fastforce
  also have "... = \<lbrace>p\<rbrace> ; ((Atomic \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
    using a1 nil_iter nondet_seq_distrib seq_magic_left seq_nil_left seq_power_Suc by fastforce
  also have "... = \<lbrace>p\<rbrace> ; ((Atomic \<^sup>;^ Suc i) \<iinter> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m))))"
    by (simp add: f_def)
  also have "... =  \<lbrace>p\<rbrace> ; ((\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (Atomic \<^sup>;^ Suc i) \<iinter> f((b\<^sub>m, c\<^sub>m))))"
    by (metis a3)
  also have "... =  \<lbrace>p\<rbrace> ; ((\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (Atomic ; (Atomic \<^sup>;^ i)) \<iinter> (atomic (b\<^sub>m)) ; c\<^sub>m))"
    using f_def by fastforce
  also have "... =  \<lbrace>p\<rbrace> ; ((\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (Atomic \<iinter> atomic (b\<^sub>m)) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m)))"
    by (metis conj.atomic_pre_sync_atomic_pre Atomic_def)
  also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m))"
    by (metis conj_atomic_sync_identity)
  finally show ?thesis .
next
  case True
  have "(Atomic \<^sup>;^ Suc i) \<iinter> c = (Atomic \<^sup>;^ Suc i) \<iinter> \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
    by (simp add: c_expanded)
  also have "... = (Atomic \<^sup>;^ Suc i) \<iinter> \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>{}))"
    by (simp add: True)
  also have "... = (Atomic ; (Atomic \<^sup>;^ i)) \<iinter> \<lbrace>p\<rbrace> ; \<tau> q"
    by fastforce
  also have "... = \<lbrace>p\<rbrace> ; \<bottom>"
    by (simp add: conj.assert_command_sync_command conj.step_sync_test)
  also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>{})"
    by simp
  also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m))"
    by (simp add: True)
  finally show ?thesis .
qed

(* The lemma in the invariants paper does not have this forall quantifier, however
   Isabelle requires it due to how the induction hypothesis is used in the proof *)
lemma atomic_iter_distrib_fixed_seq_forall:
  assumes pseudo_atomic_x[simp]: "x = atomic p \<squnion> atomic q;\<top>"
  assumes d_def[simp]: "d = x ; d \<squnion> nil"
  shows "\<forall> c\<^sub>1. (d \<otimes> ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2) = d \<otimes> ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>1) ; c\<^sub>2"
proof (induct i)
  case 0
  {
    fix c\<^sub>1
    have "(d \<otimes> ((Atomic \<^sup>;^ 0) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2) = d \<otimes> ((Atomic \<^sup>;^ 0) \<iinter> c\<^sub>1) ; c\<^sub>2"
    proof -
      obtain p q M where c1_expanded: "c\<^sub>1 = \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
        using expanded_form by blast

      have "(d \<otimes> ((Atomic \<^sup>;^ 0) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2) = (d \<otimes> (nil \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2)"
        by (metis seq_power_0)
      also have "... = (d \<otimes> (\<lbrace>p\<rbrace> ; \<tau> q)) ; (d \<otimes> c\<^sub>2)"
        by (metis c1_expanded conj.expanded_test)
      also have "... = (\<lbrace>p\<rbrace> ; \<tau> q) ; (d \<otimes> c\<^sub>2)"
        by (metis assert_distrib atomic_distributing_test pseudo_atomic_x d_def)
      also have "... = \<lbrace>p\<rbrace> ; (d \<otimes> (\<tau> q ; c\<^sub>2))"
        by (metis seq_assoc d_def pseudo_atomic_x atomic_distributing_sync_magic nonaborting_sync_test_pre_generic)
      also have "... = d \<otimes> \<lbrace>p\<rbrace> ; \<tau> q ; c\<^sub>2"
        by (metis assert_distrib seq_assoc)
      also have "... = d \<otimes> (nil \<iinter> c\<^sub>1) ; c\<^sub>2"
        by (metis c1_expanded conj.expanded_test seq_assoc)
      also have "... = d \<otimes> ((Atomic \<^sup>;^ 0) \<iinter> c\<^sub>1) ; c\<^sub>2"
        by (metis seq_power_0)
      finally show ?thesis .
    qed
  }
  then show ?case 
    by metis
next
  case (Suc i)
  {
    fix c\<^sub>1
    have "(d \<otimes> ((Atomic \<^sup>;^ Suc i) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2) = d \<otimes> ((Atomic \<^sup>;^ Suc i) \<iinter> c\<^sub>1) ; c\<^sub>2"
    proof -
      obtain p q M where c1_expanded: "c\<^sub>1 = \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
        using expanded_form by blast

      (* Defining explicit functions helps use NONDET_seq_distrib non_aborting_distrib2 *)
      define f where f_def: "f \<equiv> \<lambda> (b\<^sub>m, c\<^sub>m). atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m)" 
      define g where g_def: "g \<equiv> \<lambda> (b\<^sub>m, c\<^sub>m). d \<otimes> f((b\<^sub>m, c\<^sub>m))" 
      define h where h_def: "h \<equiv> \<lambda> (b\<^sub>m, c\<^sub>m). f((b\<^sub>m, c\<^sub>m)) ; c\<^sub>2"

      (* NONDET_seq_distrib non_aborting_distrib2 are finicky to use in Isabelle so we
         prove the steps we use them for ahead of time *)
      have dist1: "d \<otimes> (\<Squnion>m\<in>M. f(m)) = (\<Squnion>m\<in>M. d \<otimes> f(m))"
        by (metis non_aborting_distrib2 atomic_distributing_sync_magic pseudo_atomic_x d_def)
      have dist2: "(\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. g((b\<^sub>m, c\<^sub>m))) ; (d \<otimes> c\<^sub>2) = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. g((b\<^sub>m, c\<^sub>m)) ; (d \<otimes> c\<^sub>2))"
      proof -
        (* For some reason adding this k here is requried for b2 to be proven *)
        define k where k_def: "k = d \<otimes> c\<^sub>2"
        have a1: "(\<Squnion>m\<in>M. g(m)) ; k = (\<Squnion>m\<in>M. g(m) ; k)"
          by (metis NONDET_seq_distrib)
        have a2: "(\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. g((b\<^sub>m, c\<^sub>m))) ; k = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. g((b\<^sub>m, c\<^sub>m)) ; k)"
          using a1 by auto
        show ?thesis 
          by (metis a2 k_def)
      qed
      have dist3: "(\<Squnion>m\<in>M. (d \<otimes> h(m))) = (d \<otimes> (\<Squnion>m\<in>M. h(m)))"
        by (metis non_aborting_distrib2 atomic_distributing_sync_magic pseudo_atomic_x d_def)
      have dist4: "(\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m)) ; c\<^sub>2) = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m))) ; c\<^sub>2"
        by (simp add: NONDET_seq_distrib)

      (* Main proof *)
      have "(d \<otimes> ((Atomic \<^sup>;^ Suc i) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2) = (d \<otimes> \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m))) ; (d \<otimes> c\<^sub>2)"
        by (metis c1_expanded expanded_fixed_iter)
      also have "... = \<lbrace>p\<rbrace> ; (d \<otimes> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m))) ; (d \<otimes> c\<^sub>2)"
        by (metis assert_distrib)
      also have "... = \<lbrace>p\<rbrace> ; (d \<otimes> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m)))) ; (d \<otimes> c\<^sub>2)"
        using f_def by fastforce
      also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. d \<otimes> f((b\<^sub>m, c\<^sub>m))) ; (d \<otimes> c\<^sub>2)"
        using dist1 by (smt (verit) cond_case_prod_eta)
      also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. g((b\<^sub>m, c\<^sub>m))) ; (d \<otimes> c\<^sub>2)"
        using g_def by fastforce
      also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. g((b\<^sub>m, c\<^sub>m)) ; (d \<otimes> c\<^sub>2))"
        by (metis dist2 seq_assoc)
      also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (d \<otimes> (atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m))) ; (d \<otimes> c\<^sub>2))"
        using f_def g_def by fastforce
      also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. ((d \<otimes> atomic (b\<^sub>m)) ; (d \<otimes>((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m))) ; (d \<otimes> c\<^sub>2))"
        by (metis atomic_distributing_atomic_seq_command d_def pseudo_atomic_x)
      also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. ((d \<otimes> atomic (b\<^sub>m)) ; (d \<otimes> ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m) ; c\<^sub>2)))"
        by (metis seq_assoc Suc.hyps) 
      also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. d \<otimes> atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m) ; c\<^sub>2)"
        by (metis atomic_distributing_atomic_seq_command d_def pseudo_atomic_x seq_assoc)
      also have "... = \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (d \<otimes> h((b\<^sub>m, c\<^sub>m))))"
        using f_def h_def by fastforce
      also have "... = \<lbrace>p\<rbrace> ; (d \<otimes> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. h((b\<^sub>m, c\<^sub>m))))"
        by (metis (mono_tags, lifting) dist3 cond_case_prod_eta)
      also have "... = d \<otimes> \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. h((b\<^sub>m, c\<^sub>m)))"
        by (metis assert_distrib)
      also have "... = d \<otimes> \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m)) ; c\<^sub>2)"
        using h_def by fastforce
      also have "... = d \<otimes> \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m))) ; c\<^sub>2"
        by (metis dist4 seq_assoc)
      also have "... = d \<otimes> \<lbrace>p\<rbrace> ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. atomic (b\<^sub>m) ; ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>m)) ; c\<^sub>2"
        using f_def by fastforce
      also have "... = d \<otimes> ((Atomic \<^sup>;^ Suc i) \<iinter> c\<^sub>1) ; c\<^sub>2"
        by (metis c1_expanded expanded_fixed_iter)
      finally show ?thesis .
    qed
  }
  then show ?case 
    by metis
qed 

lemma atomic_iter_distrib_fixed_seq:
  assumes pseudo_atomic_x: "x = atomic p \<squnion> atomic q ; \<top>"
  assumes "d = x ; d \<squnion> nil"
  shows "(d \<otimes> ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2) = d \<otimes> ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>1) ; c\<^sub>2"
  using assms atomic_iter_distrib_fixed_seq_forall by blast

lemma atomic_iter_distrib_seq:
  assumes pseudo_atomic_x: "x = atomic p \<squnion> atomic q ; \<top>"
  assumes d_def[simp]: "d = x ; d \<squnion> nil"
  shows "(d \<otimes> c\<^sub>1) ; (d \<otimes> c\<^sub>2) = d \<otimes> (c\<^sub>1 ; c\<^sub>2)"
proof -
  define f where f_def: "f \<equiv> \<lambda> i. Atomic \<^sup>;^ i" 
  define g where g_def: "g \<equiv> \<lambda> i. f(i) \<iinter> c\<^sub>1" 
  define h where h_def: "h \<equiv> \<lambda> i. d \<otimes> g(i)" 
  define j where j_def: "j \<equiv> \<lambda> i. g(i) ; c\<^sub>2"

  have dist1: "c\<^sub>1 \<iinter> (\<Squnion>i::nat. f(i)) = (\<Squnion>i::nat. g(i))"
    by (simp add: conj.sync_NONDET_distrib conj.sync_commute g_def)
  have dist2: "d \<otimes> (\<Squnion>i::nat. g(i)) = (\<Squnion>i::nat. h(i))"
    by (metis (mono_tags, lifting) Sup.SUP_cong empty_not_UNIV h_def sync_NONDET_distrib)
  have dist3: "(\<Squnion>i::nat. h(i)) ; (d \<otimes> c\<^sub>2) = (\<Squnion>i::nat. h(i) ; (d \<otimes> c\<^sub>2))"
    by (metis NONDET_seq_distrib)
  have dist4: "(\<Squnion>i::nat. d \<otimes> j(i)) = d \<otimes> (\<Squnion>i::nat. j(i))"
    by (metis empty_not_UNIV sync_NONDET_distrib)
  have dist5: "(\<Squnion>i::nat. g(i) ; c\<^sub>2) = (\<Squnion>i::nat. g(i)) ; c\<^sub>2"
    by (simp add: NONDET_seq_distrib)

  have chaos_expanded: "chaos = (\<Squnion>i::nat. Atomic \<^sup>;^ i) \<squnion> (Atomic\<^sup>\<infinity>)"
    by (simp add: chaos_def fiter_seq_choice iter_isolation)
  have inf_conj: "(d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2) = (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1) ; c\<^sub>2)"
    by (metis (no_types, opaque_lifting) conj.inf_iter_annihilates inf_iter_annihilates infiter_unfold sync_commute)
  
  have "(d \<otimes> c\<^sub>1) ; (d \<otimes> c\<^sub>2) = (d \<otimes> (chaos \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2)"
    by (metis conj_chaos_left)
  also have "... = (d \<otimes> (((\<Squnion>i::nat. Atomic \<^sup>;^ i) \<squnion> Atomic\<^sup>\<infinity>) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2)"
    by (metis chaos_expanded)
  also have "... = (d \<otimes> ((\<Squnion>i::nat. Atomic \<^sup>;^ i) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2)"
    by (metis conj.nondet_sync_distrib nondet_seq_distrib sync_nondet_distrib)
  also have "... = (\<Squnion>i::nat. h(i) ; (d \<otimes> c\<^sub>2)) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2)"
    by (metis local.conj_commute f_def dist1 dist2 dist3)
  also have "... = (\<Squnion>i::nat. (d \<otimes> ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2)) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2)"
    using f_def g_def h_def by fastforce
  also have "... = (\<Squnion>i::nat. d \<otimes> ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>1) ; c\<^sub>2) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1)) ; (d \<otimes> c\<^sub>2)"
    by (metis pseudo_atomic_x d_def atomic_iter_distrib_fixed_seq)
  also have "... = (\<Squnion>i::nat. d \<otimes> ((Atomic \<^sup>;^ i) \<iinter> c\<^sub>1) ; c\<^sub>2) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1) ; c\<^sub>2)"
    by (metis inf_conj)
  also have "... = (\<Squnion>i::nat. d \<otimes> j(i)) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1) ; c\<^sub>2)"
    using f_def g_def j_def by fastforce
  also have "... = (d \<otimes> (\<Squnion>i::nat. j(i))) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1) ; c\<^sub>2)"
    by (metis dist4)
  also have "... = (d \<otimes> (\<Squnion>i::nat. g(i) ; c\<^sub>2)) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1) ; c\<^sub>2)"
    by (metis j_def)
  also have "... = (d \<otimes> (\<Squnion>i::nat. g(i)) ; c\<^sub>2) \<squnion> (d \<otimes> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1) ; c\<^sub>2)"
    by (metis dist5)
  also have "... = d \<otimes> (((\<Squnion>i::nat. g(i)) \<squnion> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1)) ; c\<^sub>2)"
    by (metis sync_nondet_distrib nondet_seq_distrib)
  also have "... = d \<otimes> ((c\<^sub>1 \<iinter> (\<Squnion>i::nat. f(i)) \<squnion> (Atomic\<^sup>\<infinity> \<iinter> c\<^sub>1)) ; c\<^sub>2)"
    by (metis dist1)
  also have "... = d \<otimes> ((((\<Squnion>i::nat. Atomic \<^sup>;^ i) \<squnion> Atomic\<^sup>\<infinity>) \<iinter> c\<^sub>1) ; c\<^sub>2)"
    by (metis f_def local.conj_commute conj.nondet_sync_distrib)
  also have "... = (d \<otimes> (chaos \<iinter> c\<^sub>1) ; c\<^sub>2) "
    by (metis chaos_expanded)
  also have "... = d \<otimes> c\<^sub>1 ; c\<^sub>2"
    by (metis conj_chaos_left)
  finally show ?thesis .
qed

lemma distrib_fixed_iter2:
  assumes pseudo_atomic_x: "x = atomic p \<squnion> atomic q ; \<top>"
  assumes d_def[simp]: "d = x ; d \<squnion> nil"
  shows "d \<otimes> c \<^sup>;^ i = (d \<otimes> c) \<^sup>;^ i"
proof -
  have a1: "d \<otimes> nil = nil"
    by (metis pseudo_atomic_x atomic_distributing_test d_def test_top)
  have a2: "\<forall>c\<^sub>1. d \<otimes> c ; c\<^sub>1 = (d \<otimes> c) ; (d \<otimes> c\<^sub>1)"
  proof -
    {
      fix c\<^sub>1
      have "d \<otimes> c ; c\<^sub>1 = (d \<otimes> c) ; (d \<otimes> c\<^sub>1)"
        using pseudo_atomic_x atomic_iter_distrib_seq d_def by presburger
    }
    then show ?thesis
      by (rule allI)
  qed
  show ?thesis
    by (metis a1 a2 distrib_fixed_iter)
qed

lemma distrib_finite_iter2:
  assumes pseudo_atomic_x: "x = atomic p \<squnion> atomic q ; \<top>"
  assumes d_def[simp]: "d = x ; d \<squnion> nil"
  shows "d \<otimes> c\<^sup>\<star> = (d \<otimes> c)\<^sup>\<star>"
proof -
  have a1: "d \<otimes> nil = nil"
    by (metis pseudo_atomic_x atomic_distributing_test d_def test_top)
  have a2: "\<forall>c\<^sub>1. d \<otimes> c ; c\<^sub>1 = (d \<otimes> c) ; (d \<otimes> c\<^sub>1)"
  proof -
    {
      fix c\<^sub>1
      have "d \<otimes> c ; c\<^sub>1 = (d \<otimes> c) ; (d \<otimes> c\<^sub>1)"
        using pseudo_atomic_x atomic_iter_distrib_seq d_def by presburger
    }
    then show ?thesis
      by (rule allI)
  qed
  show ?thesis
    by (metis a1 a2 distrib_finite_iter)
qed

lemma distrib_seq_pseudo_atomic_iter:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "(x\<^sup>\<omega> \<otimes> c\<^sub>1) ; (x\<^sup>\<omega> \<otimes> c\<^sub>2) = x\<^sup>\<omega> \<otimes> (c\<^sub>1 ; c\<^sub>2)"
proof -
  show ?thesis 
    by (metis atomic_iter_distrib_seq atomic_a atomic_b x_def pseudo_atomic_fixed_points_pseudo_iter)
qed

lemma distrib_seq_atomic_iter:
  assumes atomic_a[simp]: "a = (atomic p)"
  shows "(a\<^sup>\<omega> \<otimes> c\<^sub>1) ; (a\<^sup>\<omega> \<otimes> c\<^sub>2) = a\<^sup>\<omega> \<otimes> (c\<^sub>1 ; c\<^sub>2)"
proof -
  have a_expanded: "a = (atomic p) \<squnion> (atomic \<bottom>) ; \<top>"
    by simp
  show ?thesis 
    by (metis a_expanded distrib_seq_pseudo_atomic_iter)
qed

lemma atomic_iter_distrib_inf:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  assumes nil_sync_c_magic [simp]: "nil \<otimes> c = \<bottom>"
  shows "x\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> = (x\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
proof (rule antisym)
  have a1: "x\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> \<ge> (x ; x\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
    by (metis iter_to_iter_plus_iter inf_subsumes inf_sync_inf_refine)
  show "x\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> \<ge> (x\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
    by (metis a1 iter_unfold nil_sync_c_magic nondet_sync_distrib sup_bot_left)
next
  have "(x\<^sup>\<omega> \<otimes> c) ; (x\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>) \<ge> x\<^sup>\<omega> \<otimes> c ; c\<^sup>\<infinity>"
    by (simp add: distrib_seq_pseudo_atomic_iter)
  also have induction_goal: "... \<ge> x\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>"
    using calculation infiter_unfold by fastforce
  finally show "x\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> \<le> (x\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
    using induction_goal infiter_induct by auto
qed

lemma atomic_iter_distrib_iter:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  assumes "c \<otimes> nil = \<bottom>"
  shows "x\<^sup>\<omega> \<otimes> c\<^sup>\<omega> = (x\<^sup>\<omega> \<otimes> c)\<^sup>\<omega>"
proof -
  have commuted: "nil \<otimes> c = \<bottom>"
    by (simp add: assms(4) sync_commute)
  have "x\<^sup>\<omega> \<otimes> c\<^sup>\<omega> = (x\<^sup>\<omega> \<otimes> c\<^sup>\<star>) \<squnion> (x\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>)"
    by (simp add: iter_isolation sync_nondet_distrib)
  also have "... = (x\<^sup>\<omega> \<otimes> c)\<^sup>\<star> \<squnion> (x\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>)"
    by (metis atomic_a atomic_b atomic_iter_distrib_seq distrib_finite_iter pseudo_atomic_fixed_points_pseudo_iter pseudo_atomic_iter_sync_nil x_def)
  also have "... = (x\<^sup>\<omega> \<otimes> c)\<^sup>\<star> \<squnion> (x\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
    using commuted atomic_iter_distrib_inf by auto
  also have "... = (x\<^sup>\<omega> \<otimes> c)\<^sup>\<omega>"
    by (simp add: iter_isolation sync_nondet_distrib)
  finally show ?thesis .
qed

lemma seq_maintain_test:
  assumes t_def [simp]: "t = \<tau> p"
  assumes a_def [simp]: "a = atomic q"
  assumes preserve_t: "t ; a ; t = t ; a"
  shows "t ; (a\<^sup>\<omega> \<otimes> c\<^sub>1 ; c\<^sub>2) = t ; (a\<^sup>\<omega> \<otimes> c\<^sub>1) ; t ; (a\<^sup>\<omega> \<otimes> c\<^sub>2)"
proof -
  have "t ; (a\<^sup>\<omega> \<otimes> c\<^sub>1 ; c\<^sub>2) = t ; (a\<^sup>\<omega> \<otimes> c\<^sub>1) ; (a\<^sup>\<omega> \<otimes> c\<^sub>2)"
    by (simp add: distrib_seq_atomic_iter seq_assoc)
  also have "... = t ; (a\<^sup>\<omega> \<otimes> c\<^sub>1) ; t ; (a\<^sup>\<omega> \<otimes> c\<^sub>2)"
    by (metis t_def maintain_test preserve_t)
  finally show ?thesis .
qed

lemma test_atomic_iter_distrib_seq:
  assumes t_def [simp]: "t = \<tau> p"
  assumes a_def [simp]: "a = atomic q"
  assumes preserve_t: "t ; a ; t = t ; a"
  assumes "test.negate(t) ; c\<^sub>1 \<le> Atomic ; \<top>"
  shows "t ; a\<^sup>\<omega> \<otimes> c\<^sub>1 ; c\<^sub>2 = (t ; a\<^sup>\<omega> \<otimes> c\<^sub>1) ; (t ; a\<^sup>\<omega> \<otimes> c\<^sub>2)"
proof -
  have b1: "test.negate(t) ; c\<^sub>1 ; c\<^sub>2 \<otimes> \<bottom> = \<bottom>"
  proof (rule antisym)
    show "\<bottom> \<le> test.negate(t) ; c\<^sub>1 ; c\<^sub>2 \<otimes> \<bottom>" 
      by simp
  next
    have a1: "test.negate(t) ; c\<^sub>1 ; c\<^sub>2 \<otimes> \<bottom> \<le> Atomic ; \<top> \<otimes> \<bottom>"
      by (metis assms(4) seq_abort_right seq_mono_left step_sync_test test.Hom_def test.Hom_ref_hom test.hom_bot test_seq_magic)
    have a2: "Atomic ; \<top> \<otimes> \<bottom> = \<bottom>"
      by (metis seq_abort_right step_sync_test test.hom_bot)
    show "test.negate(t) ; c\<^sub>1 ; c\<^sub>2 \<otimes> \<bottom> \<le> \<bottom>"
      by (metis a1 a2)
  qed

  have b2: "test.negate(t) ; c\<^sub>1 \<otimes> \<bottom> = \<bottom>"
  proof (rule antisym)
    show "\<bottom> \<le> test.negate(t) ; c\<^sub>1 \<otimes> \<bottom>" 
      by simp
  next
    have a1: "test.negate(t) ; c\<^sub>1 \<otimes> \<bottom> \<le> Atomic ; \<top> \<otimes> \<bottom>"
      by (metis assms(4) sync_mono_left)
    have a2: "Atomic ; \<top> \<otimes> \<bottom> = \<bottom>"
      by (metis seq_abort_right step_sync_test test.hom_bot)
    show "test.negate(t) ; c\<^sub>1 \<otimes> \<bottom> \<le> \<bottom>"
      by (metis a1 a2)
  qed 

  have b3: "t ; (a\<^sup>\<omega> \<otimes> c\<^sub>2) = t ; (t ; a\<^sup>\<omega> \<otimes> c\<^sub>2)"
  proof -
    have "t ; (a\<^sup>\<omega> \<otimes> c\<^sub>2) = t ; t ; a\<^sup>\<omega> \<otimes> t ; c\<^sub>2"
      using test_seq_idem test_sync_distrib by auto
    also have "... = t ; (t ; a\<^sup>\<omega> \<otimes> c\<^sub>2)"
      by (simp add: seq_assoc test_sync_distrib)
    finally show ?thesis .
  qed

  have "t ; a\<^sup>\<omega> \<otimes> c\<^sub>1 ; c\<^sub>2 = t ; (a\<^sup>\<omega> \<otimes> c\<^sub>1 ; c\<^sub>2)"
    using b1 seq_assoc sync_commute t_def test_command_sync_command by auto
  also have "... = t ; (a\<^sup>\<omega> \<otimes> c\<^sub>1) ; t ; (t ; a\<^sup>\<omega> \<otimes> c\<^sub>2)"
    by (metis t_def a_def preserve_t seq_maintain_test b3 seq_assoc)
  also have "... = t ; (a\<^sup>\<omega> \<otimes> c\<^sub>1) ; (t ; a\<^sup>\<omega> \<otimes> c\<^sub>2)"
    by (metis maintain_test t_def preserve_t)
  also have "... = (t ; a\<^sup>\<omega> \<otimes> c\<^sub>1) ; (t ; a\<^sup>\<omega> \<otimes> c\<^sub>2)"
    using b2 sync_commute test_command_sync_command by fastforce
  finally show ?thesis .
qed

lemma atomic_iter_distrib_inf_iter:
  assumes a_def [simp]: "a = atomic q"
  assumes c_not_test: "c \<le> Atomic ; \<top>"
  shows "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> = (a ; a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
proof (rule antisym)
  show "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> \<ge> (a ; a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
    by (metis iter_to_iter_plus_iter inf_subsumes inf_sync_inf_refine)
next
  have induction_goal: "(a ; a\<^sup>\<omega> \<otimes> c) ; (a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>) \<ge> (a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>)"
  proof -
    have "(a ; a\<^sup>\<omega> \<otimes> c) ; (a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>) = (a\<^sup>\<omega> \<otimes> c) ; (a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>)"
      by (metis c_not_test at_least_once)
    also have "... = a\<^sup>\<omega> \<otimes> c ; c\<^sup>\<infinity>"
      by (simp add: distrib_seq_atomic_iter)
    also have "... = a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>"
      by (metis infiter_unfold)
    finally show ?thesis
      by simp
  qed
  show "a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> \<le> (a ; a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
    using induction_goal infinite_iteration.infiter_induct infinite_iteration_axioms by blast
qed

lemma atomic_inv_distrib_inf_iter:
  assumes t_def [simp]: "t = \<tau> p"
  assumes a_def [simp]: "a = atomic q"
  assumes c_takes_step: "c \<le> Atomic ; \<top>"
  assumes "a = a ; t"
  shows "t ; a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> = (t ; a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
proof -
  have negate_seq_c: "test.negate(t) ; c \<le> Atomic ; \<top>"
    by (metis c_takes_step nil_ref_test seq_mono seq_nil_left t_def test.hom_not)

  have a1: "test.negate(t) ; c\<^sup>\<infinity> \<otimes> \<bottom> = \<bottom>"
  proof (rule antisym)
    show "test.negate(t) ; c\<^sup>\<infinity> \<otimes> \<bottom> \<ge> \<bottom>"
      by simp
  next
    have "test.negate(t) ; c\<^sup>\<infinity> \<otimes> \<bottom> = (test.negate(t) ; c) ; c\<^sup>\<infinity> \<otimes> \<bottom>"
      by (metis infiter_unfold seq_assoc)
    also have "... \<le> Atomic ; \<top> ; c\<^sup>\<infinity> \<otimes> \<bottom>"
      using negate_seq_c seq_mono_left sync_mono_left by fastforce
    also have "... \<le> Atomic ; \<top> \<otimes> \<bottom>"
      by (simp add: seq_assoc)
    also have "... \<le> \<bottom>"
      by (metis Atomic_def dual_order.refl sync_commute test.hom_bot test_sync_atomic_pre)
    finally show "test.negate(t) ; c\<^sup>\<infinity> \<otimes> \<bottom> \<le> \<bottom>" .
  qed

  have "t ; a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity> = t ; (a\<^sup>\<omega> \<otimes> c\<^sup>\<infinity>)"
    by (metis a1 sync_commute t_def test_command_sync_command)
  also have "... = t ; (a ; a\<^sup>\<omega> \<otimes> c)\<^sup>\<infinity>"
    by (simp add: c_takes_step atomic_iter_distrib_inf_iter)
  also have "... = t ; (a ; a\<^sup>\<omega> ; t \<otimes> c)\<^sup>\<infinity>"
    by (metis assms(4) iter_leapfrog seq_assoc)
  also have "... = t ; ((a ; a\<^sup>\<omega> \<otimes> c) ; t)\<^sup>\<infinity>"
    by (simp add: sync_commute test_sync_post)
  also have "... = (t ; (a ; a\<^sup>\<omega> \<otimes> c))\<^sup>\<infinity>"
    by (metis infinite_leapfrog)
  also have "... = (t ; (a\<^sup>\<omega> \<otimes> c))\<^sup>\<infinity>"
    by (simp add: at_least_once c_takes_step)
  finally show ?thesis
    by (metis c_takes_step nonaborting_sync_test_pre_generic seq_nil_right step_sync_test sync_commute sync_nil_magic t_def test_top)
qed

end

end