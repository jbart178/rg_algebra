theory Abstract_Atomic_Sync_Test
imports
    "../AbstractTests/Test_Commands"
    "../AbstractAtomic/Abstract_Atomic_Sync"
begin

locale atomic_sync_command_with_tests = sync_command_with_tests + atomic_sync_pre
                                        + atomic_sync sync  seq nil atomic
  + assumes expanded_form: "\<exists> p q M. c = \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))" 

begin

(* Since we 'renamed' the atomic_sync locale by instantiating it, 
   we lost all mixfix syntax of definitions inside it. Let's 
   redeclare it here.  *)
notation 
  infiter ("_\<^sup>\<infinity>" [105] 106) and
  iter  ("_\<^sup>\<omega>" [103] 102) and
  fiter ("_\<^sup>\<star>" [101] 100) and
  seq_power (infixr "\<^sup>;^" 80)

lemma test_sync_atomic_pre: "(\<tau> p) \<otimes> ((atomic r) ; c) = \<bottom>"
    by (metis sup_eq_bot_iff nondet_sync_distrib nil_sync_atomic_pre test_nondet_compl) 

lemma expanded_form_sync_magic:
  shows "(\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m) \<otimes> \<bottom> = \<bottom>"
proof -
  have magic_sync_magic: "\<bottom> \<otimes> \<bottom> = \<bottom>"
    by (metis test.hom_bot test_sync_idem)
  define f where f_def: "f \<equiv> \<lambda> (b\<^sub>m, c\<^sub>m). (atomic (b\<^sub>m)) ; c\<^sub>m" 

  have "(\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m) \<otimes> \<bottom> = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f((b\<^sub>m, c\<^sub>m))) \<otimes> \<bottom>"
    using f_def by fastforce
  also have "... = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. \<bottom> \<otimes> f((b\<^sub>m, c\<^sub>m)))"
    by (simp add: magic_sync_magic non_aborting_distrib2 sync_commute) 
  also have "... = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. \<bottom> \<otimes> (atomic (b\<^sub>m)) ; c\<^sub>m)"
    using f_def by fastforce
  also have "... = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. \<bottom>)"
    by (metis test.hom_bot test_sync_atomic_pre)
  also have "... = \<bottom>"
    by simp
  finally show ?thesis .
qed

(* Note that this is the simplest locale that has tests and iteration
   so some test related properties are proven here despite not
   involving atomic commands *)
lemma establish_test:
  assumes t_def [simp]: "t = \<tau> p"
  assumes preserve_t: "t ; c ; t = t ; c"
  shows "t ; c\<^sup>\<omega> = t ; (c ; t)\<^sup>\<omega>"
proof (rule antisym)
  have add_t_ref: "c \<ge> c ; t"
    by (metis nil_ref_test seq_mono_right seq_nil_right t_def)
  show "t ; c\<^sup>\<omega> \<ge> t ; (c ; t)\<^sup>\<omega>"
    using add_t_ref iter_mono seq_mono_right by auto
next
  have a1: "nil \<squnion> c ; t ; t ; c\<^sup>\<omega> = nil \<squnion> c ; t ; c\<^sup>\<omega>"
    using seq_assoc test_seq_idem by auto
  have a2: "nil \<squnion> c ; t ; t ; c\<^sup>\<omega> \<ge> t \<squnion> t ; c ; t ; c\<^sup>\<omega>"
    by (metis a1 nil_ref_test seq_mono_left seq_nil_left sup.mono t_def)
  have a3: "nil \<squnion> c ; t ; t ; c\<^sup>\<omega> \<ge> t ; (nil \<squnion> c ; c\<^sup>\<omega>)"
    by (metis a2 preserve_t seq_assoc seq_nil_right seq_nondet_distrib)
  have iter_induction_condition: "nil \<squnion> c ; t ; t ; c\<^sup>\<omega> \<ge> t ; c\<^sup>\<omega>"
    by (metis a3 iter_unfold)
  have iter_induction_goal: "(c ; t)\<^sup>\<omega> \<ge> t ; c\<^sup>\<omega>"
    using iter_induct_nil iter_induction_condition seq_assoc by auto
  show "t ; c\<^sup>\<omega> \<le> t ; (c ; t)\<^sup>\<omega>"
    using iter_induction_goal test_seq_refine by auto
qed

lemma preserve_test:
  assumes t_def [simp]: "t = \<tau> p"
  assumes preserve_t: "t ; c ; t = t ; c"
  shows "t ; c\<^sup>\<omega> ; t = t ; c\<^sup>\<omega>"
proof -
  have "t ; c\<^sup>\<omega> ; t = t ; (c ; t)\<^sup>\<omega> ; t"
    using establish_test preserve_t by auto
  also have "... = (t ; c)\<^sup>\<omega> ; t ; t"
    by (simp add: iter_leapfrog)
  also have "... = t ; (c ; t)\<^sup>\<omega>"
    using iter_leapfrog seq_assoc test_seq_idem by auto
  finally show ?thesis using establish_test preserve_t by auto
qed

lemma equivalent_under_inv:
  assumes t_def [simp]: "t = \<tau> p"
  assumes "t ; c\<^sub>1 ; t = t ; c\<^sub>1"
  assumes "t ; c\<^sub>1 = t ; c\<^sub>2"
  shows "t ; c\<^sub>1\<^sup>\<omega> = t ; c\<^sub>2\<^sup>\<omega>"
proof -
  have "t ; c\<^sub>1\<^sup>\<omega> = t ; (c\<^sub>1 ; t)\<^sup>\<omega>"
    using establish_test assms by auto
  also have "... = t ; (c\<^sub>2 ; t)\<^sup>\<omega>"
    by (metis iter_leapfrog assms(3))
  finally show ?thesis
    using establish_test assms by auto
qed

lemma atomic_test_sync_iter_test:
  assumes a_atomic[simp]: "a = (atomic r)"
  shows  "(\<tau> p1) \<otimes> a\<^sup>\<omega>;(\<tau> p2) = (\<tau> (p1 \<sqinter> p2))"
proof -
  have "(\<tau> p1) \<otimes> a\<^sup>\<omega>;(\<tau> p2) = (\<tau> p1) \<otimes> (nil \<squnion> a;a\<^sup>\<omega>);(\<tau> p2)"
    using iter_unfold by simp
  also have "... = (\<tau> p1) \<otimes> ((\<tau> p2) \<squnion> a;a\<^sup>\<omega>;(\<tau> p2))"
    using nondet_seq_distrib by simp
  also have "... = ((\<tau> p1) \<otimes> (\<tau> p2)) \<squnion> ((\<tau> p1) \<otimes> a;(a\<^sup>\<omega>;(\<tau> p2)))"
    using sync_commute nondet_sync_distrib seq_assoc by simp
  also have "... = (\<tau> (p1 \<sqinter> p2))"
    using a_atomic test_sync_atomic_pre test_sync_test by simp
  finally show ?thesis .
qed

lemma atomic_test_sync_fiter_iter_test:
  assumes a_atomic[simp]: "a = (atomic r1)"
  assumes b_atomic[simp]: "b = (atomic r2)"
  shows  "(\<tau> p1) \<otimes> a\<^sup>\<star>;b\<^sup>\<omega>;(\<tau> p2) = (\<tau> (p1 \<sqinter> p2))"
proof -
  have "(\<tau> p1) \<otimes> a\<^sup>\<star>;b\<^sup>\<omega>;(\<tau> p2) = (\<tau> p1) \<otimes> (nil \<squnion> a;a\<^sup>\<star>);b\<^sup>\<omega>;(\<tau> p2)"
    using fiter_unfold by simp
  also have "... = (\<tau> p1) \<otimes> (b\<^sup>\<omega>;(\<tau> p2) \<squnion> a;a\<^sup>\<star>;b\<^sup>\<omega>;(\<tau> p2))"
    using nondet_seq_distrib by simp
  also have "... = ((\<tau> p1) \<otimes> b\<^sup>\<omega>;(\<tau> p2)) \<squnion> ((\<tau> p1) \<otimes> a;a\<^sup>\<star>;b\<^sup>\<omega>;(\<tau> p2))"
    using sync_commute nondet_sync_distrib seq_assoc by simp
  also have "... = (\<tau> (p1 \<sqinter> p2))"
    using atomic_test_sync_iter_test b_atomic
          a_atomic test_sync_atomic_pre seq_assoc by simp
  finally show ?thesis .
qed

lemma atomic_test_helper1: "a\<^sup>\<omega>;b \<squnion> b = a\<^sup>\<omega>;b"
proof -
  have "a\<^sup>\<omega>;b \<squnion> b = (nil \<squnion> a;a\<^sup>\<omega>);b \<squnion> b"
    using iter_unfold by simp
  also have "... = (nil \<squnion> a;a\<^sup>\<omega>);b"
    by (simp add: sup_commute nondet_seq_distrib)
  also have "... = a\<^sup>\<omega>;b"
    using iter_unfold by simp
  finally show ?thesis .
qed
    
(* can be reduced to a\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>  by setting a = c, p2 = \<top>
    for showing (guar g);\<tau>(p) \<iinter> term = ((guar g) \<iinter> term);\<tau>(p) *)
lemma atomic_fiter_iter_test_sync_fiter_iter_test:
  assumes a_atomic[simp]: "a = (atomic r1)"
  assumes b_atomic[simp]: "b = (atomic r2)"
  assumes c_atomic[simp]: "c = (atomic r3)"
  assumes d_atomic[simp]: "d = (atomic r4)"
  shows "a\<^sup>\<star>;c\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) =
          (a\<otimes>b)\<^sup>\<star>;((c\<otimes>b)\<^sup>\<star> \<squnion> (a\<otimes>d)\<^sup>\<star>);(c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
proof -
  have  "a\<^sup>\<star>;c\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) = (a\<otimes>b)\<^sup>\<star>;(
        (c\<otimes>b)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;((\<tau> p2) \<otimes> c\<^sup>\<omega>;(\<tau> p1) \<squnion> d\<^sup>\<omega>;(\<tau> p2) \<otimes> (\<tau> p1)) \<squnion> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) \<otimes> (\<tau> p1)) \<squnion>
        (a\<otimes>d)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;((\<tau> p1) \<otimes> d\<^sup>\<omega>;(\<tau> p2) \<squnion> c\<^sup>\<omega>;(\<tau> p1) \<otimes> (\<tau> p2)) \<squnion> a\<^sup>\<star>;c\<^sup>\<omega>;(\<tau> p1) \<otimes> (\<tau> p2)))"
    using atomic_fiter_iter_pre_sync_fiter_iter_pre by simp
  also have  "... = (a\<otimes>b)\<^sup>\<star>;(
        (c\<otimes>b)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2)) \<squnion> \<tau> (p1 \<sqinter> p2)) \<squnion>
        (a\<otimes>d)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2)) \<squnion> \<tau> (p1 \<sqinter> p2)))"
    using a_atomic b_atomic c_atomic d_atomic sync_commute
    by (simp add: atomic_test_sync_iter_test atomic_test_sync_fiter_iter_test inf_commute) 
  also have  "... = (a\<otimes>b)\<^sup>\<star>;((c\<otimes>b)\<^sup>\<star> \<squnion> (a\<otimes>d)\<^sup>\<star>);((c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2)) \<squnion> \<tau> (p1 \<sqinter> p2))"
    by (simp add: nondet_seq_distrib seq_assoc)
  also have  "... = (a\<otimes>b)\<^sup>\<star>;((c\<otimes>b)\<^sup>\<star> \<squnion> (a\<otimes>d)\<^sup>\<star>);(c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
    using atomic_test_helper1 seq_assoc by simp
  finally show ?thesis .
qed

lemma atomic_iter_test_sync_fiter_iter_test:
  assumes a_atomic[simp]: "a = (atomic r1)"
  assumes b_atomic[simp]: "b = (atomic r2)"
  assumes d_atomic[simp]: "d = (atomic r4)"
  shows "a\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) = (a\<otimes>b)\<^sup>\<star>;(a\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
proof -
  have "a\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) = a\<^sup>\<star>;a\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2)"
    by (simp add: fiter_seq_iter)
  also have "... = (a\<otimes>b)\<^sup>\<star>;((a\<otimes>b)\<^sup>\<star> \<squnion> (a\<otimes>d)\<^sup>\<star>);(a\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
    using atomic_fiter_iter_test_sync_fiter_iter_test by simp
  also have "... = (a\<otimes>b)\<^sup>\<star>;(a\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
    by (simp add: fiter_seq_iter nondet_seq_distrib seq_assoc seq_nondet_distrib)
  finally show ?thesis . 
qed

lemma distrib_finite_iter:
  assumes nil_sync[simp]: "d \<otimes> nil = nil"
  assumes sync_distr[simp]: "\<forall>c\<^sub>1. d \<otimes> c ; c\<^sub>1 = (d \<otimes> c) ; (d \<otimes> c\<^sub>1)"
  shows "d \<otimes> c\<^sup>\<star> = (d \<otimes> c)\<^sup>\<star>"
proof -
  define F where "F = (\<lambda> y . d \<otimes> y)"
  define G where "G = (\<lambda> y . nil \<squnion> c ; y)"
  define H where "H = (\<lambda> y . nil \<squnion> (d \<otimes> c) ; y)"
  have G_lfp: "lfp G = c\<^sup>\<star>"
    using fiter_def G_def by auto
  have H_lfp: "lfp H = (d \<otimes> c)\<^sup>\<star>"
    using fiter_def H_def by auto
  have F_comp_lfp_G: "F(lfp G) = d \<otimes> c\<^sup>\<star>"
    by (simp add: F_def G_lfp)
  (* Proof uses fusion to show "F(lfp G) = lfp H 
     Need to show F continuous, G and H monotonic, F \<circ> G = H \<circ> F *)

  (* need d \<otimes> \<bottom> = \<bottom> to show F is continuous*)
  have "nil \<otimes> \<bottom> = (\<tau> top) \<otimes> (\<tau> \<bottom>)"
    by (simp add: nil_def)
  then have nil_sync_bot: "... = \<bottom>"
    by (metis nil_inf_test test.hom_bot test_sync_test test_top)
  have d_sync_magic: "d \<otimes> \<bottom> = \<bottom>"
  proof -
    have "d \<otimes> \<bottom> = d \<otimes> (nil \<otimes> \<bottom>)"
      using nil_sync_bot test_top by fastforce 
    also have "... = (d \<otimes> nil) \<otimes> \<bottom>"
      by (metis sync_assoc)
    also have "... = nil \<otimes> \<bottom>"
      by (metis nil_sync)
    also have "... = \<bottom>"
      using nil_sync_bot test_top by force
    finally show ?thesis .
  qed

  (* F is continuous *)
  have F_cont: "dist_over_nondet F" 
    using d_sync_magic non_aborting_distrib F_def by fastforce

  (* G is monotonic *)
  have G_mono: "mono G"
  proof -
    have a1: "\<forall>x y. x \<le> y \<longrightarrow> G(x) \<le> nil \<squnion> c ; y"
      by (metis G_def inf_sup_ord(4) seq_mono_right sup.idem sup.mono)
    have a2: "\<forall>x y. x \<le> y \<longrightarrow> G(x) \<le> G(y)"
      by (metis a1 G_def)
    show ?thesis
      by (simp add: a2 mono_def)
   qed

  (* H is monotonic *)
  have H_mono: "mono H"
  proof -
    have a1: "\<forall>x y.  x \<le> y \<longrightarrow>  H(x) \<le> nil \<squnion> (d \<otimes> c) ; y"
      using H_def seq_mono_right sup.mono by blast
    have a2: "\<forall>x y.  x \<le> y \<longrightarrow> H(x) \<le> H(y)"
      by (metis a1 H_def)
    show ?thesis
      by (simp add: a2 mono_def)
  qed

  (* F \<circ> G = H \<circ> F *)
  have comp_equal: "\<And>x. ((F \<circ> G) x = (H \<circ> F) x)"
  proof -
    have a1: "\<And>x. ((F \<circ> G) x = d \<otimes> (nil \<squnion> c ; x))"
      by (simp add: F_def G_def)
    have a2: "\<And>x. ((F \<circ> G) x = (d \<otimes> nil) \<squnion> (d \<otimes> c ; x))"
      using a1 sync_nondet_distrib by fastforce
    have a3: "\<And>x. ((F \<circ> G) x = nil \<squnion> (d \<otimes> c) ; (d \<otimes> x))"
      using a2 by fastforce
    have a4: "\<And>x. ((F \<circ> G) x = (H \<circ> F) x)"
      using a3 F_def H_def by fastforce
    show "\<And>x. ((F \<circ> G) x = (H \<circ> F) x)" by (metis a4)
  qed

  have fusion_goal: "F(lfp G) = lfp H"
    by (metis G_mono H_mono comp_equal F_cont fusion_lfp_eq)
  show ?thesis by (metis F_comp_lfp_G H_lfp fusion_goal)
qed

lemma step_sync_test:
  assumes assump[simp]: "Atomic ; \<top> \<ge> c"
  assumes test_t[simp]: "t = \<tau> p"
  shows "c ; d \<otimes> t = \<bottom>"
proof -
  have add_sync_seq: "Atomic ; \<top> ; d \<otimes> t \<ge> c ; d \<otimes> t"
    by (simp add: seq_mono sync_mono)
  have show_magic: "Atomic ; \<top> ; d \<otimes> t = \<bottom>"
    by (simp add: test_sync_atomic_pre seq_assoc Atomic_def sync_commute)
  have less_than_magic: "\<bottom> \<ge> c ; d \<otimes> t"
    by (metis add_sync_seq show_magic)
  have greater_than_magic: "c ; d \<otimes> t \<ge> \<bottom>"
    by (simp)
  have "c ; d \<otimes> t = \<bottom>"
    by (metis less_than_magic greater_than_magic order_antisym)
  then show ?thesis using less_than_magic greater_than_magic by metis
qed

lemma iter_distrib_test:
  assumes assump[simp]: "Atomic ; \<top> \<ge> c"
  assumes test_t[simp]: "t = \<tau> p"
  shows "c\<^sup>\<omega> \<otimes> t = t"
proof -
  have "c\<^sup>\<omega> \<otimes> t = (nil \<squnion> c ; c\<^sup>\<omega>) \<otimes> t"
    by (metis iter_unfold)
  also have "... = (nil \<otimes> t) \<squnion> (c ; c\<^sup>\<omega> \<otimes> t)"
    by (metis nondet_sync_distrib)
  also have "... = t"
    by (simp add: step_sync_test test_sync_to_inf nil_def)
  finally show ?thesis .
qed

(* Useful corollary to the above lemma *)
lemma iter_distrib_magic:
  assumes assump[simp]: "Atomic ; \<top> \<ge> c"
  shows "c\<^sup>\<omega> \<otimes> \<bottom> = \<bottom>"
proof -
  have a1: "c\<^sup>\<omega> \<otimes> \<tau> bot = \<tau> bot"
    by (metis iter_distrib_test assump)
  show ?thesis using a1 by auto
qed

(* Helper for atomic_iter_distrib_atomic *)
lemma pseudo_atomic_distrib_test:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "x\<^sup>\<omega> \<otimes> \<tau> r = \<tau> r"
proof -
  have ref: "Atomic ; \<top> \<ge> x"
    by (smt (verit, best) abstract_hom_commands.Hom_ref_hom atomic.abstract_hom_commands_axioms atomic_a atomic_b dual_order.trans seq_abort_right seq_mono_left sup_least x_def)
  show ?thesis by (metis ref iter_distrib_test nil_def)
qed

(* Helper for atomic_iter_distrib_atomic *)
lemma pseudo_atomic_iter_sync_nil:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "x\<^sup>\<omega> \<otimes> nil = nil"
  by (metis atomic_a atomic_b pseudo_atomic_distrib_test test_top x_def)


lemma atomic_iter_distrib_Nondet:
  assumes assump[simp]: "Atomic ; \<top> \<ge> c"
  shows "c\<^sup>\<omega> \<otimes> (\<Squnion>D) = (\<Squnion>d \<in> D. c\<^sup>\<omega> \<otimes> d)"
  by (metis assump iter_distrib_magic non_aborting_distrib)

lemma pseudo_atomic_distrib_Nondet:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "x\<^sup>\<omega> \<otimes> (\<Squnion>D) = (\<Squnion>d \<in> D. x\<^sup>\<omega> \<otimes> d)"
proof -
  have atomic_ref_x: "Atomic ; \<top> \<ge> x"
    by (smt (verit) atomic.Hom_ref_hom atomic_a atomic_b dual_order.trans seq_abort_right seq_mono_left sup.bounded_iff x_def)
  show ?thesis
    by (metis atomic_iter_distrib_Nondet atomic_ref_x)
qed


lemma atomic_distributing_test:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes d_def[simp]: "d = (a \<squnion> b ; \<top>) ; d \<squnion> nil"
  assumes t_test[simp]: "t = \<tau> r"
  shows "d \<otimes> t = t"
proof -
  have "d \<otimes> t = ((a \<squnion> b ; \<top>) ; d \<squnion> nil) \<otimes> t"
    by (metis d_def)
  also have "... = ((a \<squnion> b ; \<top>) ; d \<otimes> t) \<squnion> (nil \<otimes> t)"
    by (metis nondet_sync_distrib)
  also have "... = (a ; d \<otimes> t \<squnion> b ; (\<top> ; d) \<otimes> t) \<squnion> t"
    by (metis nondet_seq_distrib nondet_sync_distrib sync_commute t_test test_sync_nil seq_assoc)
  also have "... = (\<bottom> \<squnion> \<bottom>) \<squnion> t"
    by (metis atomic_a atomic_b test_sync_atomic_pre sync_commute t_test)
  also have "... = t"
    by simp
  finally show ?thesis .
qed

(* Show that x\<^sup>\<star> is a pseudo atomic fixed point*)
lemma pseudo_atomic_fixed_points_pseudo_fiter:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "x\<^sup>\<star> = (a \<squnion> b ; \<top>) ; x\<^sup>\<star> \<squnion> nil"
proof -
  have "x\<^sup>\<star> = x ; x\<^sup>\<star> \<squnion> nil"
    by (metis fiter_unfold sup_commute)
  also have "... = (a \<squnion> b ; \<top>) ; x\<^sup>\<star> \<squnion> nil"
    by (metis x_def)
  finally show ?thesis .
qed

(* Show that x\<^sup>\<omega> is a pseudo atomic fixed point*)
lemma pseudo_atomic_fixed_points_pseudo_iter:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "x\<^sup>\<omega> = (a \<squnion> b ; \<top>) ; x\<^sup>\<omega> \<squnion> nil"
proof -
  have "x\<^sup>\<omega> = x ; x\<^sup>\<omega> \<squnion> nil"
    by (metis iter_unfold sup_commute)
  also have "... = (a \<squnion> b ; \<top>) ; x\<^sup>\<omega> \<squnion> nil"
    by (metis x_def)
  finally show ?thesis .
qed

(* Show that a\<^sup>\<star> is a pseudo atomic fixed point*)
lemma pseudo_atomic_fixed_points_fiter:
  assumes atomic_a[simp]: "a = (atomic p)"
  shows "a\<^sup>\<star> = (a \<squnion> atomic \<bottom> ; \<top>) ; a\<^sup>\<star> \<squnion> nil"
  by (metis atomic.hom_bot fiter_unfold seq_magic_left sup_bot.right_neutral sup_commute)

(* Show that a\<^sup>\<omega> is a pseudo atomic fixed point*)
lemma pseudo_atomic_fixed_points_iter:
  assumes atomic_a[simp]: "a = (atomic p)"
  shows "a\<^sup>\<omega> = (a \<squnion> atomic \<bottom> ; \<top>) ; a\<^sup>\<omega> \<squnion> nil"
  by (metis atomic.hom_bot iter_unfold seq_magic_left sup.commute sup_bot.right_neutral)

lemma inf_sync_inf_refine:
  shows "c\<^sup>\<infinity> \<otimes> d\<^sup>\<infinity> \<ge> (c \<otimes> d)\<^sup>\<infinity>"
  sorry

end

locale atomic_sync_command_with_tests_aborting = atomic_sync_command_with_tests 
                                                 + sync_command_with_tests_aborting
begin

lemma atomic_pre_sync_test_pre:
  shows "(atomic r);c \<otimes> (\<tau> p);d = (\<tau> p);((atomic r);c \<otimes> d)"
proof -
  have "(atomic r);c \<otimes> \<bottom> = \<bottom>"
    by (metis sync_commute test.hom_bot test_sync_atomic_pre)
  then show ?thesis using nonaborting_sync_test_pre_generic by metis
qed

lemma assert_command_sync_command: "c \<otimes> \<lbrace>p\<rbrace> ; d = \<lbrace>p\<rbrace> ; (c \<otimes> d)"
proof -
  define t where test_t [simp]: "t = \<tau> p"
  have negate_then_assert: "test.negate t ; \<lbrace>p\<rbrace> = test.negate t ; \<top>"
  proof -
    have "test.negate t ; \<lbrace>p\<rbrace> = test.negate t ; (t \<squnion> test.negate t ; \<top>)"
      by (simp add: assert_def)
    also have "... = test.negate t ; t \<squnion> test.negate t ; test.negate t ; \<top>"
      by (simp add: seq_assoc seq_nondet_distrib)
    also have "... = test.negate t ; t \<squnion> test.negate t ; \<top>"
      using test_seq_idem by auto  
    finally show ?thesis 
      by (metis seq_nondet_distrib sup_top_right)
  qed

  have "c \<otimes> \<lbrace>p\<rbrace> ; d = (t \<squnion> test.negate t) ; (c \<otimes> \<lbrace>p\<rbrace> ; d)"
    using test_nondet_compl by auto
  also have "... = t ; (c \<otimes> \<lbrace>p\<rbrace> ; d) \<squnion> test.negate t ; (c \<otimes> \<lbrace>p\<rbrace> ; d)"
    by (simp add: nondet_seq_distrib)
  also have "... = (t ; c \<otimes> t ; \<lbrace>p\<rbrace> ; d)  \<squnion> (test.negate t ; c \<otimes> test.negate t ; \<lbrace>p\<rbrace> ; d)"
    by (simp add: seq_assoc test_sync_distrib)
  also have "... = (t ; c \<otimes> t ; d)  \<squnion> (test.negate t ; c \<otimes> test.negate t ; \<top>)"
    by (metis test_t test_seq_assert negate_then_assert seq_assoc seq_abort)
  also have "... = t ; (c \<otimes> d)  \<squnion> test.negate t ; (c \<otimes> \<top>)"
    by (simp add: test_sync_distrib)
  also have "... = t ; (c \<otimes> d) \<squnion> test.negate t ; \<top>"
    by (metis sync_abort_right)
  also have "... = t ; (c \<otimes> d) \<squnion> test.negate t ; \<top> ; (c \<otimes> d)"
    by (simp add: sync_abort_left seq_assoc)
  also have "... = \<lbrace>p\<rbrace> ; (c \<otimes> d)"
    by (simp add: assert_def nondet_seq_distrib)
  finally show ?thesis .
qed

lemma expanded_test:
  assumes c_expanded: "c = \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
  shows "nil \<otimes> c = \<lbrace>p\<rbrace> ; \<tau> q"
proof -
  have a1: "\<tau> p ; (nil \<otimes> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m)) = \<bottom>"
  proof -
    have b1: "nil \<otimes> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m) = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. nil \<otimes> (atomic (b\<^sub>m)) ; c\<^sub>m)"
    proof -
      define f where f_def [simp]: "f \<equiv> \<lambda> (b\<^sub>m, c\<^sub>m). (atomic (b\<^sub>m)) ; c\<^sub>m"
      have nil_sync_magic: "nil \<otimes> \<bottom> = \<bottom>"
        by (metis sync_commute test.hom_bot test_sync_nil)
      have "nil \<otimes> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m) = nil \<otimes> (\<Squnion>m\<in>M. f(m))"
        by simp
      also have "... = (\<Squnion>m\<in>M. nil \<otimes> f(m))"
        by (metis nil_sync_magic non_aborting_distrib2)
      then show ?thesis
        by (simp add: prod.case_distrib)
    qed
    have "\<tau> p ; (nil \<otimes> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m)) = \<tau> p ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. nil \<otimes> (atomic (b\<^sub>m)) ; c\<^sub>m)"
      by (metis b1)
    then show ?thesis
      by (simp add: nil_sync_atomic_pre test_seq_magic)
  qed

  have "nil \<otimes> c = nil \<otimes> \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
    by (simp add: c_expanded)
  also have "... = (nil \<otimes> \<tau> p ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))) \<squnion> \<tau>(-p) ; \<top>"
    by (simp add: assert_def nondet_seq_distrib seq_assoc sync_nondet_distrib nil_sync_test_pre sync_abort_right)
  also have "... = (nil \<otimes> \<tau> p ; \<tau> q \<squnion> nil \<otimes> \<tau> p ; (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m)) \<squnion> \<tau>(-p) ; \<top>"
    by (simp add: seq_nondet_distrib sync_nondet_distrib)
  also have "... = \<tau> p ; (nil \<otimes> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m)) \<squnion> \<tau>(p \<sqinter> q) \<squnion> \<tau>(-p) ; \<top>"
    by (metis (no_types, lifting) nil_sync_test_pre boolean_algebra_cancel.sup1 boolean_algebra_cancel.sup2 test_sync_nil sync_commute test_seq_test)
  also have "... = \<bottom> \<squnion> \<tau>(p \<sqinter> q) \<squnion> \<tau>(-p) ; \<top>"
    by (metis a1)
  also have "... = \<tau> p ; \<tau> q \<squnion> \<tau>(-p) ; \<top>"
    by (simp add: test_seq_magic test_seq_test)
  also have "... = \<lbrace>p\<rbrace> ; \<tau> q"
    by (simp add: assert_def inf_sup_aci(5) nondet_seq_distrib seq_assoc test_seq_magic)
  finally show ?thesis .
qed

lemma sync_nil_magic_takes_step_forward:
  assumes "Atomic ; \<top> \<ge> c"
  shows "c \<otimes> nil = \<bottom>"
proof -
  have a1: "c \<otimes> nil \<le> Atomic ; \<top> \<otimes> nil"
    by (simp add: assms sync_mono_left)
  have a2: "Atomic ; \<top> \<otimes> nil = \<bottom>"
    by (simp add: Atomic_def atomic_pre_sync_nil)
  show ?thesis
    using a1 a2 order_antisym by fastforce
qed

lemma sync_nil_magic_takes_step_reverse:
  assumes "c \<otimes> nil = \<bottom>"
  shows "Atomic ; \<top> \<ge> c"
proof -
  obtain p q M where c_expanded: "c = \<lbrace>p\<rbrace> ; (\<tau> q \<squnion> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m))"
    using expanded_form by blast

  have magic_expanded: "\<bottom> = \<tau> p ; \<tau> q \<squnion> test.negate (\<tau> p) ; \<top>"
    using assert_def assms c_expanded expanded_test nondet_seq_distrib seq_assoc sync_commute by auto
  have p_nil: "\<tau> p = nil"
  proof -
    have right_term: "\<bottom> = test.negate (\<tau> p) ; \<top>"
      using magic_expanded by auto
    have "\<bottom> = test.negate (\<tau> p)"
      by (metis bot.extremum_uniqueI right_term seq_abort_right)
    then show ?thesis
      by (metis sup_bot.right_neutral test_nondet_compl)
  qed
  have assert_nil: "\<lbrace>p\<rbrace> = nil"
    by (metis p_nil seq_nil_left test_seq_assert)
  have q_magic: "\<tau> q = \<bottom>"
    using magic_expanded p_nil by auto

  have c_simplified: "c = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. (atomic (b\<^sub>m)) ; c\<^sub>m)"
    by (simp add: assert_nil c_expanded q_magic)
  show "Atomic ; \<top> \<ge> c"
  proof (cases "M = {}")
    case False
    define f where f_def: "f \<equiv> \<lambda> (b\<^sub>m, c\<^sub>m). atomic (b\<^sub>m) ; c\<^sub>m"
    have a1: "\<forall>(b\<^sub>m, c\<^sub>m)\<in>M. Atomic ; \<top> \<ge> f(b\<^sub>m, c\<^sub>m)"
      using atomic.Hom_ref_hom seq_mono f_def by auto
    have a2: "Atomic ; \<top> = (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. Atomic ; \<top>)"
      by (simp add: False)
    have a3: "Atomic ; \<top> \<ge> (\<Squnion>(b\<^sub>m, c\<^sub>m)\<in>M. f(b\<^sub>m, c\<^sub>m))"
      using a1 a2 SUP_le_iff by auto
    show ?thesis 
      using a3 f_def c_simplified by fastforce
  next
    case True
    have c_magic: "c = \<bottom>"
      by (simp add: True c_simplified)
    show ?thesis
      by (simp add: c_magic)
  qed
qed

lemma sync_nil_magic_takes_step: "Atomic ; \<top> \<ge> c \<longleftrightarrow> c \<otimes> nil = \<bottom>"
  using sync_nil_magic_takes_step_forward sync_nil_magic_takes_step_reverse by blast

lemma iter_distrib_assert:
  assumes assump[simp]: "Atomic ; \<top> \<ge> c"
  assumes test_t[simp]: "t = \<tau> p"
  shows "c\<^sup>\<omega> \<otimes> (assert p) = (assert p)"
proof -
  have test_seq_iter_magic: "t ; c\<^sup>\<omega> \<otimes> \<bottom> = \<bottom>"
  proof -
    have "t ; c\<^sup>\<omega> \<otimes> \<bottom> = t ; (c\<^sup>\<omega> \<otimes> \<bottom>)"
      by (simp add: test_seq_magic test_sync_distrib)
    also have "... = t ; \<bottom>"
      by (metis assump iter_distrib_magic)
    also have "... = \<bottom>"
      by (simp add: test_seq_magic)
    finally show ?thesis .
  qed

  have "c\<^sup>\<omega> \<otimes> (assert p) = c\<^sup>\<omega> \<otimes> ((\<tau> p) \<squnion> test.negate (\<tau> p) ; \<top>)"
    by (metis assert_def)
  also have "... = (c\<^sup>\<omega> \<otimes> (\<tau> p)) \<squnion> (c\<^sup>\<omega> \<otimes> test.negate (\<tau> p) ; \<top>)"
    by (simp add: sync_nondet_distrib)
  also have "... = (\<tau> p) \<squnion> (c\<^sup>\<omega> \<otimes> test.negate (\<tau> p) ; \<top>)"
    by (simp add: iter_distrib_test)
  also have "... = (\<tau> p) \<squnion> test.negate (\<tau> p) ; (c\<^sup>\<omega> \<otimes> \<top>)"
    using test_command_sync_command test_seq_iter_magic by fastforce
  also have "... = (\<tau> p) \<squnion> test.negate (\<tau> p) ; \<top>"
    by (metis sync_abort_right)
  also have "... = assert p"
    by (metis assert_def)
  finally show ?thesis .
qed

lemma pseudo_atomic_distrib_assert:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "x\<^sup>\<omega> \<otimes> (assert r) = (assert r)"
  by (metis atomic_a atomic_b nil_sync_assert pseudo_atomic_iter_sync_nil sync_assoc x_def)

lemma pseudo_atomic_merge_helper:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  shows  "a\<^sup>\<omega> ; (nil \<squnion> b ; \<top>) \<otimes> nil = nil"
proof - 
  have "a\<^sup>\<omega> ; (nil \<squnion> b ; \<top>) \<otimes> nil = (nil \<squnion> b ; \<top>) \<otimes> nil"
    by (simp add: atomic_iter_pre_sync_nil)
  also have "... = nil \<otimes> nil \<squnion> (b ; \<top>) \<otimes> nil"
    by (simp add: nondet_sync_distrib)
  also have "... = nil"
    by (simp add: nil_sync_nil sync_commute nil_sync_atomic_pre)
  finally show ?thesis .
qed

lemma pseudo_atomic_merge_helper2:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes atomic_c[simp]: "c = (atomic r)"
  shows "(b ; \<top> \<otimes> a\<^sup>\<omega> ; (nil \<squnion> c ; \<top>)) = (b \<otimes> (a \<squnion> c)) ; \<top>"
proof - 
  have "(b ; \<top> \<otimes> a\<^sup>\<omega> ; (nil \<squnion> c ; \<top>)) = (b ; \<top> \<otimes> (nil \<squnion> a ; a\<^sup>\<omega>) ; (nil \<squnion> c ; \<top>))"
    using iter_unfold by fastforce
  also have "... = b ; \<top> \<otimes> ((nil ; (nil \<squnion> c ; \<top>)) \<squnion> (a ; a\<^sup>\<omega> ; (nil \<squnion> c ; \<top>)))"
    by (simp add: nondet_seq_distrib)
  also have "... = (b ; \<top> \<otimes> nil \<squnion> b ; \<top> \<otimes> c ; \<top>) \<squnion> (b ; \<top> \<otimes> a ; a\<^sup>\<omega> ; (nil \<squnion> c ; \<top>))"
    by (simp add: sync_nondet_distrib)
  also have "... = (nil \<otimes> b ; \<top> \<squnion> b ; \<top> \<otimes> c ; \<top>) \<squnion> (b ; \<top> \<otimes> a ; (a\<^sup>\<omega> ; (nil \<squnion> c ; \<top>)))"
    by (simp add: sync_commute seq_assoc)
  also have "... = ((b \<otimes> c) ; (\<top> \<otimes> \<top>)) \<squnion> ((b \<otimes> a) ; (\<top> \<otimes> a\<^sup>\<omega> ; (nil \<squnion> c ; \<top>)))"
    by (simp add: nil_sync_atomic_pre atomic_pre_sync_atomic_pre)
  also have "... = ((b \<otimes> c) ; \<top>) \<squnion> ((b \<otimes> a) ; \<top>)"
    by (simp add: atomic_pre_sync_atomic_pre sync_abort_left)
  also have "... = ((b \<otimes> c) \<squnion> (b \<otimes> a)) ; \<top>"
    by (simp add: nondet_seq_distrib)
  also have "... = (b \<otimes> (a \<squnion> c)) ; \<top>"
    by (simp add: sync_nondet_distrib sup_commute)
  finally show ?thesis .
qed

lemma pseudo_atomic_merge:
  assumes atomic_a1[simp]: "a\<^sub>1 = (atomic p\<^sub>1)"
  assumes atomic_a2[simp]: "a\<^sub>2 = (atomic p\<^sub>2)"
  assumes atomic_b1[simp]: "b\<^sub>1 = (atomic q\<^sub>1)"
  assumes atomic_b2[simp]: "b\<^sub>2 = (atomic q\<^sub>2)"
  assumes a_sync[simp]: "a = a\<^sub>1 \<otimes> a\<^sub>2"
  assumes b_def[simp]: "b = (b\<^sub>1 \<otimes> a\<^sub>2) \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) \<squnion> (a\<^sub>1 \<otimes> b\<^sub>2)"
  shows "(a\<^sub>1 \<squnion> b\<^sub>1 ; \<top>)\<^sup>\<omega> \<otimes> (a\<^sub>2 \<squnion> b\<^sub>2 ; \<top>)\<^sup>\<omega> = (a \<squnion> b ; \<top>)\<^sup>\<omega>"
proof - 
  have atomic_a: "\<exists>p . a = (atomic p)"
    by (simp add: atomic_sync)
  have atomic_b3: "\<exists>r . (b\<^sub>1 \<otimes> a\<^sub>2) = (atomic r)"
    by (simp add: atomic_sync)
  have atomic_b4: "\<exists>s . (b\<^sub>1 \<otimes> b\<^sub>2) = (atomic s)"
    by (simp add: atomic_sync)
  have atomic_b5: "\<exists>t . (a\<^sub>1 \<otimes> b\<^sub>2) = (atomic t)"
    by (simp add: atomic_sync)
  have atomic_b6: "\<exists>r s t . b = (atomic r) \<squnion> (atomic s) \<squnion> (atomic t)"
    by (metis atomic_b3 atomic_b4 atomic_b5 b_def)
  have atomic_b: "\<exists>q . b = (atomic q)"
    by (metis atomic_b6 atomic.hom_sup)
  have "(a\<^sub>1 \<squnion> b\<^sub>1 ; \<top>)\<^sup>\<omega> \<otimes> (a\<^sub>2 \<squnion> b\<^sub>2 ; \<top>)\<^sup>\<omega> = a\<^sub>1\<^sup>\<omega> ; (nil \<squnion> b\<^sub>1 ; \<top>) \<otimes> a\<^sub>2\<^sup>\<omega> ; (nil \<squnion> b\<^sub>2 ; \<top>)"
    by (simp add: iter_or_abort_alt)
  also have "... = a\<^sup>\<omega> ; ((nil \<squnion> b\<^sub>1 ; \<top>) \<otimes> a\<^sub>2\<^sup>\<omega> ; (nil \<squnion> b\<^sub>2 ; \<top>) 
      \<squnion> a\<^sub>1\<^sup>\<omega> ; (nil \<squnion> b\<^sub>1 ; \<top>) \<otimes> (nil \<squnion> b\<^sub>2 ; \<top>))"
    by (simp add: atomic_iter_pre_sync_iter_pre2)
  also have "... = a\<^sup>\<omega> ; 
        ((nil \<otimes> a\<^sub>2\<^sup>\<omega> ; (nil \<squnion> b\<^sub>2 ; \<top>)) 
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> a\<^sub>2\<^sup>\<omega> ; (nil \<squnion> b\<^sub>2 ; \<top>)) 
      \<squnion> (a\<^sub>1\<^sup>\<omega> ; (nil \<squnion> b\<^sub>1 ; \<top>) \<otimes> nil) 
      \<squnion> (a\<^sub>1\<^sup>\<omega> ; (nil \<squnion> b\<^sub>1 ; \<top>) \<otimes> b\<^sub>2 ; \<top>))"
    by (simp add: nondet_sync_distrib sync_nondet_distrib sup_assoc)
  also have "... = a\<^sup>\<omega> ; 
        ((a\<^sub>2\<^sup>\<omega> ; (nil \<squnion> b\<^sub>2 ; \<top>) \<otimes> nil) 
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> a\<^sub>2\<^sup>\<omega> ; (nil \<squnion> b\<^sub>2 ; \<top>)) 
      \<squnion> (a\<^sub>1\<^sup>\<omega> ; (nil \<squnion> b\<^sub>1 ; \<top>) \<otimes> nil) 
      \<squnion> (a\<^sub>1\<^sup>\<omega> ; (nil \<squnion> b\<^sub>1 ; \<top>) \<otimes> b\<^sub>2 ; \<top>))"
    by (simp add: sync_commute)
  also have "... = a\<^sup>\<omega> ; 
        (nil
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> a\<^sub>2\<^sup>\<omega> ; (nil \<squnion> b\<^sub>2 ; \<top>)) 
      \<squnion> nil
      \<squnion> (a\<^sub>1\<^sup>\<omega> ; (nil \<squnion> b\<^sub>1 ; \<top>) \<otimes> b\<^sub>2 ; \<top>))"
    by (simp add: pseudo_atomic_merge_helper)
  also have "... = a\<^sup>\<omega> ; 
        (nil
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> a\<^sub>2\<^sup>\<omega> ; (nil \<squnion> b\<^sub>2 ; \<top>)) 
      \<squnion> (b\<^sub>2 ; \<top> \<otimes> a\<^sub>1\<^sup>\<omega> ; (nil \<squnion> b\<^sub>1 ; \<top>)))"
    by (simp add: nil_sync_nil sync_commute nil_sync_atomic_pre sup_commute)
  also have "... = a\<^sup>\<omega> ; 
        (nil
      \<squnion> ((b\<^sub>1 \<otimes> (a\<^sub>2 \<squnion> b\<^sub>2)) ; \<top>) 
      \<squnion> ((b\<^sub>2 \<otimes> (a\<^sub>1 \<squnion> b\<^sub>1)); \<top>))"
    by (simp add: pseudo_atomic_merge_helper2)
  also have "... = a\<^sup>\<omega> ; 
        (nil
      \<squnion> ((b\<^sub>1 \<otimes> a\<^sub>2 \<squnion> b\<^sub>1 \<otimes> b\<^sub>2) ; \<top>)
      \<squnion> ((b\<^sub>2 \<otimes> a\<^sub>1 \<squnion> b\<^sub>2 \<otimes> b\<^sub>1)) ; \<top>)"
    by (simp add: sync_nondet_distrib sup_assoc)
  also have "... = a\<^sup>\<omega> ; 
        (nil
      \<squnion> ((b\<^sub>1 \<otimes> a\<^sub>2) ; \<top> \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) ; \<top>)
      \<squnion> ((a\<^sub>1 \<otimes> b\<^sub>2) ; \<top> \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) ; \<top>))"
    by (simp add: nondet_seq_distrib sync_commute)
  also have "... = a\<^sup>\<omega> ; (nil \<squnion> (b\<^sub>1 \<otimes> a\<^sub>2) ; \<top> \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) ; \<top> \<squnion> ((b\<^sub>2 \<otimes> a\<^sub>1) ; \<top> \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) ; \<top>))"
    by (simp add: sync_commute sup_assoc) 
  also have "... = a\<^sup>\<omega> ; (nil \<squnion> (b\<^sub>1 \<otimes> a\<^sub>2) ; \<top> \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) ; \<top> \<squnion> ((b\<^sub>1 \<otimes> b\<^sub>2) ; \<top> \<squnion> (b\<^sub>2 \<otimes> a\<^sub>1) ; \<top>))"
    by (simp add: sup_commute) 
  also have "... = a\<^sup>\<omega> ; (nil \<squnion> (b\<^sub>1 \<otimes> a\<^sub>2) ; \<top> \<squnion> ((b\<^sub>1 \<otimes> b\<^sub>2) ; \<top> \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) ; \<top>) \<squnion> (b\<^sub>2 \<otimes> a\<^sub>1) ; \<top>)"
    by (simp add: sup_assoc) 
  also have "... = a\<^sup>\<omega> ; (nil \<squnion> ((b\<^sub>1 \<otimes> a\<^sub>2) ; \<top> \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) ; \<top> \<squnion> (a\<^sub>1 \<otimes> b\<^sub>2) ; \<top>))"
    by (simp add: sync_commute sup_assoc) 
  also have "... = a\<^sup>\<omega> ; (nil \<squnion> b ; \<top>)"
    by (simp add: nondet_seq_distrib) 
  also have "... = (a \<squnion> b ; \<top>)\<^sup>\<omega>"
    by (metis iter_or_abort_alt atomic_a atomic_b)
  finally show ?thesis .
qed

lemma pseudo_atomic_seq:
  assumes atomic_a[simp]: "a\<^sub>1 = (atomic p\<^sub>1)"
  assumes atomic_a2[simp]: "a\<^sub>2 = (atomic p\<^sub>2)"
  assumes atomic_b[simp]: "b\<^sub>1 = (atomic q\<^sub>1)"
  assumes atomic_b2[simp]: "b\<^sub>2 = (atomic q\<^sub>2)"
  assumes x1_def[simp]: "x\<^sub>1 = a\<^sub>1 \<squnion> b\<^sub>1 ; \<top>"
  assumes x2_def[simp]: "x\<^sub>2 = a\<^sub>2 \<squnion> b\<^sub>2 ; \<top>"
  shows "x\<^sub>1 ; c\<^sub>1 \<otimes> x\<^sub>2 ; c\<^sub>2 = (x\<^sub>1 \<otimes> x\<^sub>2) ; (c\<^sub>1 \<otimes> c\<^sub>2)"
proof -
  have "x\<^sub>1 ; c\<^sub>1 \<otimes> x\<^sub>2 ; c\<^sub>2 = (a\<^sub>1 \<squnion> b\<^sub>1 ; \<top>) ; c\<^sub>1 \<otimes> (a\<^sub>2 \<squnion> b\<^sub>2 ; \<top>) ; c\<^sub>2"
    by (simp)
  also have "... = (a\<^sub>1 ; c\<^sub>1 \<squnion> b\<^sub>1 ; (\<top> ; c\<^sub>1)) \<otimes> (a\<^sub>2 ; c\<^sub>2 \<squnion> b\<^sub>2 ; (\<top> ; c\<^sub>2))"
    by (simp add: nondet_seq_distrib seq_assoc)
  also have "... = (a\<^sub>1 ; c\<^sub>1 \<squnion> b\<^sub>1 ; \<top>) \<otimes> (a\<^sub>2 ; c\<^sub>2 \<squnion> b\<^sub>2 ; \<top>)"
    by (simp)
  also have "... = 
      (a\<^sub>1 ; c\<^sub>1 \<otimes> a\<^sub>2 ; c\<^sub>2)
      \<squnion> (a\<^sub>1 ; c\<^sub>1 \<otimes> b\<^sub>2 ; \<top>)
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> a\<^sub>2 ; c\<^sub>2)
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> b\<^sub>2 ; \<top>)"
    by (simp add: nondet_sync_product)
  also have "... = 
      ((a\<^sub>1 \<otimes> a\<^sub>2) ; (c\<^sub>1 \<otimes> c\<^sub>2))
      \<squnion> ((a\<^sub>1 \<otimes> b\<^sub>2) ; (c\<^sub>1 \<otimes> \<top>))
      \<squnion> ((b\<^sub>1 \<otimes> a\<^sub>2) ; (\<top> \<otimes> c\<^sub>2))
      \<squnion> ((b\<^sub>1 \<otimes> b\<^sub>2) ; (\<top> \<otimes> \<top>))"
    by (simp add: atomic_pre_sync_atomic_pre)
  also have "... = 
      ((a\<^sub>1 \<otimes> a\<^sub>2) ; (c\<^sub>1 \<otimes> c\<^sub>2))
      \<squnion> ((a\<^sub>1 \<otimes> b\<^sub>2) ; (c\<^sub>1 \<otimes> \<top>))
      \<squnion> ((b\<^sub>1 \<otimes> a\<^sub>2) ; (c\<^sub>2 \<otimes> \<top>))
      \<squnion> ((b\<^sub>1 \<otimes> b\<^sub>2) ; (\<top> \<otimes> \<top>))"
    by (simp add: sync_commute)
  also have "... = 
      ((a\<^sub>1 \<otimes> a\<^sub>2) ; (c\<^sub>1 \<otimes> c\<^sub>2))
      \<squnion> (((a\<^sub>1 \<otimes> b\<^sub>2) ; \<top>)
      \<squnion> ((b\<^sub>1 \<otimes> a\<^sub>2) ; \<top>)
      \<squnion> ((b\<^sub>1 \<otimes> b\<^sub>2) ; \<top>))"
    by (simp add: sup_assoc sync_abort_right)
  also have "... = 
      (a\<^sub>1 \<otimes> a\<^sub>2) ; (c\<^sub>1 \<otimes> c\<^sub>2)
      \<squnion> (((a\<^sub>1 \<otimes> b\<^sub>2) \<squnion> (b\<^sub>1 \<otimes> a\<^sub>2) \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2)) ; \<top>) ; (c\<^sub>1 \<otimes> c\<^sub>2)"
    by (simp add: nondet_seq_distrib seq_assoc)
  also have "... = ((a\<^sub>1 \<otimes> a\<^sub>2) \<squnion> ((a\<^sub>1 \<otimes> b\<^sub>2) \<squnion> (b\<^sub>1 \<otimes> a\<^sub>2) \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2)) ; \<top>) ; (c\<^sub>1 \<otimes> c\<^sub>2)"
    by (simp add: nondet_seq_distrib)
  also have "... = 
      ((a\<^sub>1 \<otimes> a\<^sub>2)
      \<squnion> (a\<^sub>1 \<otimes> b\<^sub>2) ; \<top>
      \<squnion> (b\<^sub>1 \<otimes> a\<^sub>2) ; \<top>
      \<squnion> (b\<^sub>1 \<otimes> b\<^sub>2) ; (\<top> \<otimes> \<top>))
      ; (c\<^sub>1 \<otimes> c\<^sub>2)"
    by (simp add: nondet_seq_distrib sup_assoc sync_abort_right)
  also have "... = 
     ((a\<^sub>1 \<otimes> a\<^sub>2)
      \<squnion> ((a\<^sub>1 \<otimes> b\<^sub>2) ; (nil \<otimes> \<top>))
      \<squnion> ((b\<^sub>1 \<otimes> a\<^sub>2) ; (\<top> \<otimes> nil))
      \<squnion> ((b\<^sub>1 \<otimes> b\<^sub>2) ; (\<top> \<otimes> \<top>)))
      ; (c\<^sub>1 \<otimes> c\<^sub>2)"
    by (simp add: sync_commute sync_abort_left)
  also have "... = 
      ((a\<^sub>1 \<otimes> a\<^sub>2)
       \<squnion> ((a\<^sub>1 \<otimes> b\<^sub>2) ; (nil \<otimes> \<top>))
      \<squnion> ((b\<^sub>1 \<otimes> a\<^sub>2) ; (\<top> \<otimes> nil))
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> b\<^sub>2 ; \<top>))
      ; (c\<^sub>1 \<otimes> c\<^sub>2)"
    by (simp add: atomic_pre_sync_atomic_pre)
  also have "... = 
      ((a\<^sub>1 \<otimes> a\<^sub>2)
      \<squnion> (a\<^sub>1 ; nil \<otimes> b\<^sub>2 ; \<top>)
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> a\<^sub>2 ; nil)
      \<squnion> (b\<^sub>1 ; \<top> \<otimes> b\<^sub>2 ; \<top>))
      ; (c\<^sub>1 \<otimes> c\<^sub>2)"
    by (simp add: atomic_pre_sync_atomic_pre nil_def)
  also have "... = ((a\<^sub>1 \<squnion> b\<^sub>1 ; \<top>) \<otimes> (a\<^sub>2 \<squnion> b\<^sub>2 ; \<top>)) ; (c\<^sub>1 \<otimes> c\<^sub>2)"
    by (simp add: nondet_sync_product)
  also have "... = (x\<^sub>1 \<otimes> x\<^sub>2) ; (c\<^sub>1 \<otimes> c\<^sub>2)"
    by (simp)
  finally show ?thesis .
qed

lemma atomic_iter_distrib_atomic_seq:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes atomic_a1[simp]: "a\<^sub>1 = (atomic p\<^sub>1)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "x\<^sup>\<omega> \<otimes> a\<^sub>1 ; c = (x \<otimes> a\<^sub>1) ; (x\<^sup>\<omega> \<otimes> c)"
proof - 
  have a1_pseudo_atomic: "a\<^sub>1 = (atomic p\<^sub>1) \<squnion> (atomic bot) ; \<top>"
    by (simp)
  have "x\<^sup>\<omega> \<otimes> a\<^sub>1 ; c = (nil \<squnion> x ; x\<^sup>\<omega>) \<otimes> a\<^sub>1 ; c"
    using iter_unfold by fastforce
  also have "... = x ; x\<^sup>\<omega> \<otimes> a\<^sub>1 ; c"
    by (simp add: nondet_sync_distrib nil_sync_atomic_pre)
  also have "... = (x \<otimes> a\<^sub>1) ; (x\<^sup>\<omega> \<otimes> c)"
    by (metis pseudo_atomic_seq atomic_a atomic_b atomic_a1 x_def a1_pseudo_atomic)
  finally show ?thesis .
qed

lemma atomic_iter_distrib_atomic:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes atomic_a1[simp]: "a\<^sub>1 = (atomic p\<^sub>1)"
  assumes x_def[simp]: "x = a \<squnion> b ; \<top>"
  shows "x\<^sup>\<omega> \<otimes> a\<^sub>1 = x \<otimes> a\<^sub>1"
proof - 
  have "x\<^sup>\<omega> \<otimes> a\<^sub>1 = x\<^sup>\<omega> \<otimes> a\<^sub>1 ; nil"
    by (metis seq_nil_right)
  also have "... = (x \<otimes> a\<^sub>1) ; (x\<^sup>\<omega> \<otimes> nil)"
    by (metis atomic_a atomic_b atomic_a1 x_def atomic_iter_distrib_atomic_seq nil_def)
  also have "... = (x \<otimes> a\<^sub>1) ; nil"
    by (simp add: pseudo_atomic_iter_sync_nil)
  also have "... = x \<otimes> a\<^sub>1"
    by (metis seq_nil_right)
  finally show ?thesis .
qed

lemma inf_iter_annihilates:
  shows "(c\<^sup>\<infinity> \<otimes> d\<^sub>1) ; d\<^sub>2 = c\<^sup>\<infinity> \<otimes> d\<^sub>1"
proof -
  have "(c\<^sup>\<infinity> \<otimes> d\<^sub>1) ; d\<^sub>2 = (c\<^sup>\<omega> ; \<tau> bot \<otimes> d\<^sub>1) ; d\<^sub>2"
    by (simp add: infiter_iter_magic)
  also have "... = (c\<^sup>\<omega> \<otimes> d\<^sub>1) ; \<tau> bot ; d\<^sub>2"
    by (metis test_sync_post sync_commute seq_assoc)
  also have "... = (c\<^sup>\<omega> \<otimes> d\<^sub>1) ; \<tau> bot"
    by (simp add: seq_assoc)
  also have "... = (c\<^sup>\<omega> ; \<tau> bot \<otimes> d\<^sub>1)"
    by (metis test_sync_post sync_commute)
  also have "... = c\<^sup>\<infinity> \<otimes> d\<^sub>1"
    by (simp add: infiter_iter_magic)
  finally show ?thesis .
qed

lemma inf_subsumes:
  shows "c\<^sup>\<omega> \<otimes> d\<^sup>\<infinity> = c\<^sup>\<infinity> \<otimes> d\<^sup>\<infinity>"
proof -
  have "c\<^sup>\<omega> \<otimes> d\<^sup>\<infinity> = c\<^sup>\<omega> \<otimes> d\<^sup>\<infinity> ; \<tau> bot"
    by (simp add: infiter_annil)
  also have "... = (c\<^sup>\<omega> \<otimes> d\<^sup>\<infinity>) ; \<tau> bot"
    by (metis test_sync_post)
  also have "... = c\<^sup>\<omega> ; \<tau> bot \<otimes> d\<^sup>\<infinity>"
    by (metis sync_commute test_sync_post)
  also have "... = c\<^sup>\<infinity> \<otimes> d\<^sup>\<infinity>"
    by (simp add: infiter_iter_magic)
  finally show ?thesis .
qed

lemma at_least_once2:
  assumes nil_sync_d: "nil \<otimes> d = \<bottom>"
  shows "c\<^sup>\<omega> \<otimes> d = c ; c\<^sup>\<omega> \<otimes> d"
proof -
  have "c\<^sup>\<omega> \<otimes> d = (nil \<squnion> c ; c\<^sup>\<omega>) \<otimes> d"
    by (metis iter_unfold)
  also have "... = (nil \<otimes> d) \<squnion> (c ; c\<^sup>\<omega> \<otimes> d)"
    by (metis nondet_sync_distrib)
  also have "... = c ; c\<^sup>\<omega> \<otimes> d"
    by (simp add: nil_sync_d)
  finally show ?thesis .
qed

(* Old statement of at_least_once, directly implied by at_least_once2 *)
lemma at_least_once:
  assumes psuedo_atomic_d[simp]: "Atomic ; \<top> \<ge> d"
  shows "c\<^sup>\<omega> \<otimes> d = c ; c\<^sup>\<omega> \<otimes> d"
  using at_least_once2 sync_commute sync_nil_magic_takes_step_forward by force

lemma assert_distrib: "\<lbrace>p\<rbrace>;(c \<otimes> d) = c \<otimes> (\<lbrace>p\<rbrace>;d)"
proof -
  have "(c \<otimes> \<lbrace>p\<rbrace>;d) = ((\<tau> p);(c \<otimes> \<lbrace>p\<rbrace>;d) \<squnion> (\<tau>(-p));(c \<otimes> \<lbrace>p\<rbrace>;d))"
    by (metis nondet_seq_distrib seq_nil_left test.hom_not test_nondet_compl)
  also have "\<dots> = ((\<tau> p);c \<otimes> (\<tau> p);\<lbrace>p\<rbrace>;d) \<squnion> (\<tau>(-p);c \<otimes> \<tau>(-p);\<lbrace>p\<rbrace>;d)"
    by (simp add: seq_assoc test_sync_distrib)
  also have "\<dots> = ((\<tau> p);c \<otimes> (\<tau> p);d) \<squnion> (\<tau>(-p);c \<otimes> \<tau>(-p);\<lbrace>-p\<rbrace>;\<lbrace>p\<rbrace>;d)"
    using test_seq_assert by simp
  also have "\<dots> = (\<tau> p);(c \<otimes> d) \<squnion> (\<tau>(-p);c \<otimes> \<tau>(-p);\<top>)"
    using assert_seq_compl assert_seq_assert seq_assoc test_sync_distrib by force
  also have "\<dots> = (\<tau> p);(c \<otimes> d) \<squnion> \<tau>(-p);\<top>"
    by (metis sync_abort_left local.sync_commute test_sync_distrib)
  also have "\<dots> = (\<tau> p);(c \<otimes> d) \<squnion> \<tau>(-p);\<top>;(c \<otimes> d)"
    by (simp add: seq_assoc)
  finally show ?thesis
    by (simp add: assert_def nondet_seq_distrib) 
qed

lemma atomic_distributing_atomic_seq_command:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  assumes atomic_a1[simp]: "a\<^sub>1 = (atomic p\<^sub>1)"
  assumes d_def[simp]: "d = (a \<squnion> b ; \<top>) ; d \<squnion> nil"
  shows "d \<otimes> a\<^sub>1 ; c = (d \<otimes> a\<^sub>1) ; (d \<otimes> c)"
proof -
  have d_sync_a1: "d \<otimes> a\<^sub>1 = (a \<otimes> a\<^sub>1) \<squnion> (b \<otimes> a\<^sub>1) ; \<top>"
  proof -
    have "d \<otimes> a\<^sub>1 = ((a \<squnion> b ; \<top>) ; d \<squnion> nil) \<otimes> a\<^sub>1 ; nil"
      by (metis d_def seq_nil_right)
    also have "... = (a ; d \<squnion> b ; \<top> ; d \<squnion> nil) \<otimes> a\<^sub>1 ; nil"
      by (metis nondet_seq_distrib)
    also have "... = a ; d \<otimes> a\<^sub>1 ; nil \<squnion> b ; \<top> ; d\<otimes> a\<^sub>1 ; nil \<squnion> nil \<otimes> a\<^sub>1 ; nil"
      by (metis nondet_sync_distrib seq_assoc)
    also have "... = a ; d \<otimes> a\<^sub>1 ; nil \<squnion> b ; (\<top> ; d) \<otimes> a\<^sub>1 ; nil"
      by (metis nil_def atomic_a1 test_sync_atomic_pre sup_bot_right seq_assoc)
    also have "... = (a \<otimes> a\<^sub>1) ; (d \<otimes> nil) \<squnion> (b \<otimes> a\<^sub>1) ; (\<top> ; d \<otimes> nil)"
      by (metis atomic_pre_sync_atomic_pre atomic_a atomic_b atomic_a1)
    also have "... = (a \<otimes> a\<^sub>1) \<squnion> (b \<otimes> a\<^sub>1) ; (\<top> ; d \<otimes> nil)"
      by (metis atomic_distributing_test atomic_a atomic_b d_def nil_def seq_nil_right)
    also have "... = (a \<otimes> a\<^sub>1) \<squnion> (b \<otimes> a\<^sub>1) ; \<top>"
      by (metis seq_abort sync_abort_left)
    finally show ?thesis .
  qed

  have "d \<otimes> a\<^sub>1 ; c = ((a \<squnion> b ; \<top>) ; d \<squnion> nil) \<otimes> a\<^sub>1 ; c"
    by (metis d_def)
  also have "... = ((a \<squnion> b ; \<top>) ; d \<otimes> a\<^sub>1 ; c) \<squnion> (nil \<otimes> a\<^sub>1 ; c)"
    by (metis nondet_sync_distrib)
  also have "... =  (((a \<otimes> a\<^sub>1) \<squnion> (b \<otimes> a\<^sub>1) ; \<top>) ; (d \<otimes> c)) \<squnion> \<bottom>"
    using test_sync_atomic_pre test_sync_test
    by (smt (verit) atomic_a atomic_a1 atomic_b atomic_pre_sync_atomic_pre nil_sync_atomic_pre nondet_seq_distrib nondet_sync_distrib seq_abort seq_assoc sync_abort_right sync_commute)
  also have "... = (d \<otimes> a\<^sub>1) ; (d \<otimes> c)"
    by (metis d_sync_a1 sup_bot_right)
  finally show ?thesis .
qed

(* Helper for atomic_iter_distrib_fixed_seq *)
lemma atomic_distributing_sync_magic: 
  assumes atomic_a[simp]: "a = (atomic g)"
  assumes atomic_b[simp]: "b = (atomic h)"
  assumes d_def[simp]: "d = (a \<squnion> b ; \<top>) ; d \<squnion> nil"
  shows "d \<otimes> \<bottom> = \<bottom>"
  by (metis atomic_a atomic_b atomic_distributing_test d_def test.hom_bot)

(* Helper for atomic_iter_distrib_fixed_seq *)
lemma pseudo_atomic_iter_sync_magic: 
  assumes atomic_a[simp]: "a = (atomic g)"
  assumes atomic_b[simp]: "b = (atomic h)"
  assumes x_def[simp]: "x = (a \<squnion> b ; \<top>)"
  shows "x\<^sup>\<omega> \<otimes> \<bottom> = \<bottom>"
proof -
  show ?thesis 
    by (metis atomic_a atomic_b x_def atomic_distributing_sync_magic pseudo_atomic_fixed_points_pseudo_iter)
qed

lemma maintain_test:
  assumes t_def [simp]: "t = \<tau> p"
  assumes preserve_t: "t ; c ; t = t ; c"
  shows "t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1) ; t = t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)"
proof -
  have "t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1) ; t = (t ; c\<^sup>\<omega> \<otimes> t ; c\<^sub>1) ; t"
    by (simp add: test_sync_distrib)
  also have "... = t ; c\<^sup>\<omega> ; t \<otimes> t ; c\<^sub>1"
    by (simp add: test_sync_post sync_commute)
  also have "... = t ; c\<^sup>\<omega> \<otimes> t ; c\<^sub>1"
    using preserve_test preserve_t by auto
  finally show ?thesis by (simp add: test_sync_distrib)
qed

lemma finite_iter_maintain_test:
  assumes t_def [simp]: "t = \<tau> p"
  assumes preserve_t: "t ; c ; t = t ; c"
  shows "t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<star> = t ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star>"
proof (rule antisym)
  have add_t_ref: "c \<ge> c ; t"
    by (metis nil_ref_test seq_mono_right seq_nil_right t_def)
  show "t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<star> \<ge> t ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star>"
    by (metis fiter_mono nil_ref_test seq_mono_left seq_mono_right seq_nil_left t_def)
next
  have a1: "(t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star> \<ge> t ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star>"
    by (simp add: test_seq_refine)
  have a2: "(t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star> \<ge> t \<squnion> t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1) ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star>"
    by (metis fiter_unfold inf_sup_ord(4) le_supI1 nil_ref_test sup.bounded_iff t_def)
  have a3: "(t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star> \<ge> t \<squnion> t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1) ; \<lbrace>p\<rbrace> ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star>"
    by (metis (full_types) a2 maintain_test preserve_t seq_assoc t_def test_seq_assert)
  have induction_condition: "\<lbrace>p\<rbrace> ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star> \<ge> nil \<squnion> (c\<^sup>\<omega> \<otimes> c\<^sub>1) ; \<lbrace>p\<rbrace> ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star>"
    using a3 assert_galois_test seq_assoc test_nondet_distrib by auto
  have induction_goal: "\<lbrace>p\<rbrace> ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star> \<ge> (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<star>"
    using fiter_induct_nil induction_condition seq_assoc by fastforce
  show "t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<star> \<le> t ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<star>"
    by (metis assert_galois_test induction_goal t_def test_seq_refine)
qed

lemma iter_maintain_test:
  assumes t_def [simp]: "t = \<tau> p"
  assumes preserve_t: "t ; c ; t = t ; c"
  shows "t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<omega> = t ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<omega>"
proof (rule antisym)
  have add_t_ref: "c \<ge> c ; t"
    by (metis nil_ref_test seq_mono_right seq_nil_right t_def)
  show "t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<omega> \<ge> t ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<omega>"
    by (metis iter_mono nil_ref_test seq_mono_left seq_mono_right seq_nil_left t_def)
next
  have a1: "t \<squnion> t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1) ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<omega> \<ge> t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<omega>"
    by (metis iter_unfold seq_assoc seq_nil_right t_def test_nondet_distrib_weak)
  have induction_condition: "nil \<squnion> t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1) ; t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<omega> \<ge> t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<omega>"
    by (metis a1 maintain_test preserve_t seq_nil_right t_def test_nondet_distrib test_seq_idem test_seq_refine)
  have induction_goal: "(t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<omega> \<ge> t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<omega>"
    using induction_condition iter_induct_nil seq_assoc by auto
  show "t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1)\<^sup>\<omega> \<le> t ; (t ; (c\<^sup>\<omega> \<otimes> c\<^sub>1))\<^sup>\<omega>"
    using induction_goal test_seq_refine by auto
qed

end

end