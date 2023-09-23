section \<open>Assignments under interference\<close>
theory Assignments
imports
  State_Relations
  Expressions
begin (*declare [[show_types]]*)
                                      
locale assignments = expressions + state_relations + 
  (* for lib_last :: "'k \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("L\<^sup>C\<^sub>_ _" [999, 999] 999) + *)
  constrains set_var :: "'k \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 'b"
  constrains get_var :: "'k \<Rightarrow> 'b \<Rightarrow> 'v"
begin

text \<open>A relation that updates $x$ to be the value $k$, leaving all other variables unchanged.\<close>
definition update :: "'k \<Rightarrow> 'v \<Rightarrow> ('b \<times>'b) set" where
  "update x k \<equiv> id_bar{|x|} \<triangleright> var_eq x k"

lemma update_nochange: "update x k \<subseteq> id_bar{|x|}"
  by (simp add: range_restrict_remove update_def) 

lemma update_eq: "update x k \<subseteq> {(s,s'). get_var x s' = k}"
  by (simp add: id_bar_def range_restricts_contains update_def var_eq_def)

text \<open>An assignment command (non-atomically) evaluates its expression $e$ to a value $k$ 
  and then atomically updates $x$ to $k$.
  The final $idle$ command and the use of an optional step ensure that
  the definition is closed under finite stuttering.\<close>
definition assign :: "'k \<Rightarrow> ('b, 'v) expr \<Rightarrow> 'a" (infix "::=" 93)
  where "x ::= e \<equiv> \<Squnion>k. \<lbrakk>e\<rbrakk>k ; opt(update x k) ; idle"

lemma id_bar_refl:
  shows "refl (id_bar vars)"
  unfolding id_bar_def refl_on_def by auto

text \<open>Below is the primary law for introducing an assignment command 
from which all other assignment laws are proven. 
The relation $g$ is required to be reflexive so that stuttering program
steps satisfy the guarantee.
It requires that the expression $e$ is single reference.
As usual when refining a specification command, its relation $q$ is required
to tolerate interference satisfying the rely relation $r$ from initial
states satisfying the precondition $p$.

The evaluation of a single-reference expression corresponds to evaluating
it in the state ($\sigma_1$) in which the single-reference variable is accessed to give some value $k$.
In that state $e$ equals $k$ and $p$ holds because $p$ is stable under $r$,
and hence $p1\,k$ is established.
Because $p1\,k$ is stable under $r$, it holds immediately before the step that
updates $x$ to be $k$. 
The single program step that updates the variable $x$ must satisfy the guarantee $g$
as well as the post-condition $q$.
\<close>

lemma rely_guar_assign:
  fixes p1::"'v \<Rightarrow> 'b set"
  assumes refl_g: "refl g"
  assumes single_reference_e: "single_reference e r"
  assumes tolerates_q: "tolerates_interference p q r"
  assumes stable_p1: "\<And>k::'v. stable (p1 k) r"
  assumes establish_p1: "\<And>k::'v. p \<inter> expr_eq e k \<subseteq> p1 k"
  assumes proviso_g: "\<And>k::'v. (p1 k) \<triangleleft> update x k \<subseteq> g"
  assumes proviso_q: "\<And>k::'v. (p1 k) \<triangleleft> update x k \<subseteq> q"
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> \<ge> x::= e"
proof - 
  have stable_p: "stable p r"
    using tolerates_q tolerates_interference_def by blast

  have refl: "refl(id_bar{|x|} \<inter> g)" 
    by (metis Int_absorb id_bar_refl refl_g refl_on_Int)

  have frame_as_guar: "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> = 
                       guar(id_bar{|x|} \<inter> g) \<iinter> rely r \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr>"
    using conj.comm.left_commute expand_frame_spec local.conj_assoc by force
  have ma: "\<dots> \<ge> (\<Squnion>k::'v. guar(id_bar{|x|} \<inter> g) \<iinter> rely r \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr>)" (is "_ \<ge> ?rhs") 
    by (simp add: local.conj_assoc)
  have mb: "\<dots> \<ge> (\<Squnion>k::'v. \<lbrakk>e\<rbrakk>k;opt(update x k);idle)"
  proof -
    have all_k: "\<And>k. guar(id_bar{|x|} \<inter> g) \<iinter> rely r \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> \<ge> 
                \<lbrakk>e\<rbrakk>k;opt(update x k);idle"
    proof -
      fix k
      have all_k_a: "rely r \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> \<ge> \<lbrakk>e\<rbrakk>k;\<lbrace>p1 k\<rbrace>;\<lparr>q\<rparr>;idle" (is "_ \<ge> ?rhs")
      proof -
        have ka: "rely r \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> = rely r \<iinter> \<lbrace>p\<rbrace>;idle;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;idle"
          using assert_seq_self tolerate_interference tolerates_q
            refine_within_rely_right by (metis conj.assert_distrib seq_assoc)
        have kb: "\<dots> \<ge> rely r \<iinter> \<lbrace>p\<rbrace>;idle;idle;\<lparr>q\<rparr>;idle" (is "_ \<ge> ?rhs")
          using idle_seq_idle assert_remove conj.sync_mono_right seq_assoc
            seq_mono_right by force
        have kc: "?rhs \<ge> rely r \<iinter> idle;\<lbrace>p\<rbrace>;idle;\<lparr>q\<rparr>;idle" (is "_ \<ge> ?rhs")
          using rely_idle_stable_assert refine_within_rely_left stable_p by presburger
        have kd: "?rhs \<ge> rely r \<iinter> idle;\<tau>(expr_eq e k);(\<lbrace>p1 k\<rbrace>;idle);\<lparr>q\<rparr>;idle"
                  (is "_ \<ge> ?rhs")
        proof-
          have intro_test: "\<lbrace>p\<rbrace> \<ge> \<tau>(expr_eq e k);\<lbrace>p1 k\<rbrace>" 
            by (metis assert_galois_test assert_iso assertions.assert_seq_assert 
                assertions_axioms establish_p1 inf_commute)
          show ?thesis using intro_test 
            by (metis conj.sync_mono_right seq_assoc seq_mono_left seq_mono_right)
        qed
        have ke: "?rhs \<ge> rely r \<iinter> (idle;\<tau>(expr_eq e k);idle);\<lbrace>p1 k\<rbrace>;\<lparr>q\<rparr>;idle"
                  (is "_ \<ge> ?rhs")
          using rely_idle_stable_assert refine_within_rely_left rely_refine_within
            stable_p1 by (metis seq_assoc)
        have kf: "?rhs \<ge> rely r \<iinter> \<lbrakk>e\<rbrakk>k;\<lbrace>p1 k\<rbrace>;\<lparr>q\<rparr>;idle" (is "_ \<ge> ?rhs")
        proof -
          have intro_e: "rely r \<iinter> idle;\<tau>(expr_eq e k);idle \<ge> rely r \<iinter> \<lbrakk>e\<rbrakk>k"
            using single_reference_eval single_reference_e 
            by (metis conj.sync_mono_right local.conj.left_idem)
          show ?thesis using intro_e refine_within_rely_left by presburger 
        qed
        have kg: "?rhs \<ge> \<lbrakk>e\<rbrakk>k;\<lbrace>p1 k\<rbrace>;\<lparr>q\<rparr>;idle" (is "_ \<ge> ?rhs")
          using rely_remove by presburger 
        show ?thesis using ka kb kc kd ke kf kg by force
      qed
      have all_k_b: "guar(id_bar{|x|} \<inter> g) \<iinter> rely r \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> \<ge> 
                     guar(id_bar{|x|} \<inter> g) \<iinter> \<lbrakk>e\<rbrakk>k;\<lbrace>p1 k\<rbrace>;\<lparr>q\<rparr>;idle" (is "_ \<ge> ?rhs") 
        using all_k_a conj.sync_mono_right local.conj_assoc seq_assoc by force 
      have mda: "?rhs \<ge> (guar(id_bar{|x|} \<inter> g) \<iinter> \<lbrakk>e\<rbrakk>k;(\<lbrace>p1 k\<rbrace>;\<lparr>q\<rparr>));
                         (guar(id_bar{|x|} \<inter> g) \<iinter> idle)" (is "_ \<ge> ?rhs")
        using guar_distrib_seq by (metis seq_assoc)
      have mdb: "?rhs \<ge> \<lbrakk>e\<rbrakk>k;(guar(id_bar{|x|} \<inter> g) \<iinter> \<lbrace>p1 k\<rbrace>;\<lparr>q\<rparr>);idle" (is "_ \<ge> ?rhs")
        using guar_distrib_seq refl eval_guar_absorb  
        by (metis dual_order.refl guar_idle seq_mono)
      have mdc: "?rhs \<ge> \<lbrakk>e\<rbrakk>k;opt(update x k);idle"
      proof -
        have opt_proviso: "(p1 k) \<triangleleft> update x k \<subseteq> id_bar{|x|} \<inter> g \<inter> q"
          using  proviso_g proviso_q update_def 
          by (simp add: inf_left_commute restrict_domain_def restrict_range_def) 
        have intro_opt: "guar(id_bar{|x|} \<inter> g) \<iinter> \<lbrace>p1 k\<rbrace>;\<lparr>q\<rparr> \<ge> opt(update x k)"
          using spec_ref_opt_guar refl opt_proviso by metis
        show ?thesis using intro_opt seq_mono_left seq_mono_right by presburger
      qed
      show "guar(id_bar{|x|} \<inter> g) \<iinter> rely r \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> \<ge> \<lbrakk>e\<rbrakk>k;opt(update x k);idle"
        using all_k_a all_k_b mda mdb mdc by force 
    qed
    show ?thesis using all_k by (simp add: SUP_le_iff)
  qed
  show ?thesis using frame_as_guar ma mb assign_def by presburger
qed

text \<open>Introduce an assignment command when the expression is both 
single-reference and invariant under the rely condition $r$.
Note that it does not constrain $x$ to be invariant under $r$.
\<close>
lemma local_expr_assign:
  assumes refl_g: "refl g"
  assumes single_reference_e: "single_reference e r"
  assumes estable_e: "estable e r"
  assumes tolerates_q: "tolerates_interference p q r"
  assumes req_g: "\<And>k::'v. (p \<inter> expr_eq e k) \<triangleleft> update x k \<subseteq> g"
  assumes req_q: "\<And>k::'v. (p \<inter> expr_eq e k) \<triangleleft> update x k \<subseteq> q"
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> \<ge> x ::= e"
proof -
  define p1 where "p1 \<equiv> (\<lambda>k. p \<inter> expr_eq e k)"
  have establish_p1: "\<And>k::'v. p \<inter> expr_eq e k \<subseteq> p1 k"
    using p1_def  by blast 
  have stable_p1: "\<And>k::'v. stable (p1 k) r"
    using estable_e p1_def
    by (metis estable_stable_eq stable_inter tolerates_q tolerates_interference_def)
  have proviso_g_q: "\<And>k::'v. (p1 k) \<triangleleft> update x k \<subseteq> g \<inter> q"
    using req_g req_q p1_def by simp 
 show ?thesis
   using rely_guar_assign refl_g single_reference_e tolerates_q stable_p1
     establish_p1 proviso_g_q by blast
qed

text \<open>The following idiom uses a choice restricted by a test to act like a let construct.\<close>

lemma let_j_e: "(\<Squnion>j. \<tau>(expr_eq e j)) = nil"
proof -
  have union: "(\<Union>j. expr_eq e j) = top"
    by (simp add: expr_eq_def subsetI subset_antisym)
  show ?thesis by (metis nil_def range_composition test_Sup union)
qed

text \<open>Introduce an assignment when the variable $x$ is constant under $r$
but the expression $e$ may be changing monotonically under $r$.
\<close>

lemma rely_guar_assignment_monotonic:
  fixes gte :: "'v \<Rightarrow> 'v \<Rightarrow> bool" (infix "\<succeq>" 50)
  assumes refl_g: "refl g"
  assumes stable_p: "stable p r"
  assumes stable_x: "r \<subseteq> id x" 
  assumes single_reference_e: "single_reference e r"
  assumes refl_gte: "reflp gte"
  assumes trans_gte: "transp gte"
  assumes assm_g: "\<And>k::'v. (p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> update x k \<subseteq> g"
  assumes decr_e_def: "decr_e = {(\<sigma>,\<sigma>'). eval e \<sigma> \<succeq> eval e \<sigma>'}"
  assumes r_decr: "r \<subseteq> decr_e"
  assumes id_dec: "p \<triangleleft> id_bar{|x|} \<subseteq> decr_e"
  assumes q_def: "q = {(\<sigma>,\<sigma>'). eval e \<sigma> \<succeq> get_var x \<sigma>' \<and> get_var x \<sigma>' \<succeq> eval e \<sigma>'}" 
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> \<ge> x ::= e"
proof -
  define px where "px \<equiv> (\<lambda>j. p \<inter> {\<sigma>. j \<succeq> eval e \<sigma>})"
  define p1 where "p1 \<equiv> (\<lambda>j k. p \<inter> {\<sigma>. j \<succeq> k \<and> k \<succeq> eval e \<sigma>})"
  define qj where "qj = (\<lambda>j. {(\<sigma>::'b,\<sigma>'). j \<succeq> get_var x \<sigma>' \<and> get_var x \<sigma>' \<succeq> eval e \<sigma>'})"

  have weaken_to_gte: "\<And>j. expr_eq e j \<subseteq> {\<sigma>. j \<succeq> eval e \<sigma>}"
    unfolding expr_eq_def using refl_gte by (simp add: Collect_mono reflp_def) 

  have strengthen: "\<And>j::'v. (p \<inter> expr_eq e j) \<triangleleft> qj j \<subseteq> q"
  proof -
    fix j
    have a: "expr_eq e j \<triangleleft> qj j \<subseteq> q" 
      unfolding expr_eq_def qj_def q_def by (simp add: domain_restricts_contains)   
    show "(p \<inter> expr_eq e j) \<triangleleft> qj j \<subseteq> q"
      using a domain_restrict_p_mono Int_lower2 by blast 
  qed
 
  have body: "\<And>j. rely r \<iinter> guar g \<iinter> (\<lbrace>p \<inter> expr_eq e j\<rbrace>; x:\<^sub>f\<lparr>q\<rparr>) \<ge> x ::= e"
  proof -
    fix j

    have establish_p1: "\<And>k. px j \<inter> expr_eq e k \<subseteq> p1 j k"
    proof -
      fix k
      have a: "{\<sigma>. j \<succeq> eval e \<sigma>} \<inter> expr_eq e k \<subseteq> {\<sigma>. j \<succeq> k}"
        unfolding expr_eq_def using Int_def by blast
      have b: "{\<sigma>. j \<succeq> eval e \<sigma>} \<inter> expr_eq e k \<subseteq> {\<sigma>. j \<succeq> k \<and> k \<succeq> eval e \<sigma>}"
        using weaken_to_gte a by blast
      show "px j \<inter> expr_eq e k \<subseteq> p1 j k" 
        unfolding px_def p1_def using b by blast
    qed

    have stable_ge_k_e: "\<And>k. stable {\<sigma>. k \<succeq> eval e \<sigma>} r"
    proof -
      fix k
      have a: "\<And>\<sigma> \<sigma>'. k \<succeq> eval e \<sigma> \<and> eval e \<sigma> \<succeq> eval e \<sigma>' \<longrightarrow> k \<succeq> eval e \<sigma>'"
        by (meson trans_gte transpE)
      have b: "stable {\<sigma>. k \<succeq> eval e \<sigma>} decr_e"
        using stable_def a decr_e_def trans_gte by blast
      show "stable {\<sigma>. k \<succeq> eval e \<sigma>} r"
        using b r_decr stable_antimono_r by blast
    qed

    have stable_p1: "\<And>k. stable (p1 j k) r"
    proof -
      fix k
      have a: "stable {\<sigma>. j \<succeq> k} r"
        by (simp add: stable_def)
      have c: "stable {\<sigma>. j \<succeq> k \<and> k \<succeq> eval e \<sigma>} r"
        using a stable_ge_k_e refl_gte stable_def by fastforce
      show "stable (p1 j k) r"
        unfolding p1_def using c stable_inter stable_p by blast
    qed

    have tolerates_q: "tolerates_interference (px j) (qj j) r"
    proof -
      have px_stable: "stable (px j) r"
        using stable_p stable_ge_k_e px_def stable_inter by blast
      have tol_r_q: "px j \<triangleleft> (r O qj j) \<subseteq> qj j"
        unfolding qj_def using domain_restrict_remove by blast 
      have tol_q_r: "px j \<triangleleft> (qj j O r) \<subseteq> qj j"
      proof -
        have r_bnd: "r \<subseteq> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>' \<and> eval e \<sigma> \<succeq> eval e \<sigma>'}"
          using stable_x id_def r_decr decr_e_def by blast 
        have comp_j_x: "qj j O r \<subseteq> {(\<sigma>,\<sigma>'). j \<succeq> get_var x \<sigma>'}"
          using qj_def r_bnd relcompE by auto  
        have comp_x_ge_e: "qj j O r \<subseteq> {(\<sigma>,\<sigma>'). get_var x \<sigma>' \<succeq> eval e \<sigma>'}"
        proof -
          have logic: "\<And>\<sigma> \<sigma>'' \<sigma>'. get_var x \<sigma>' \<succeq> eval e \<sigma>'' \<and> 
                        get_var x \<sigma>'' = get_var x \<sigma>' \<and> eval e \<sigma>'' \<succeq> eval e \<sigma>' \<longrightarrow> 
                          get_var x \<sigma>' \<succeq> eval e \<sigma>'" 
            by (meson trans_gte transpD) 
          have pairwise: "qj j O r \<subseteq> {(\<sigma>,\<sigma>'). get_var x \<sigma>' \<succeq> eval e \<sigma>'} O 
                                {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>' \<and> eval e \<sigma> \<succeq> eval e \<sigma>'}"
            using qj_def r_bnd by blast 
          show ?thesis using logic pairwise by auto
        qed
        show ?thesis 
            using comp_j_x comp_x_ge_e domain_restrict_remove qj_def by blast
      qed
      show ?thesis using px_stable tol_r_q tol_q_r tolerates_interference_def 
        by metis
    qed

    have proviso_g: "\<And>k. p1 j k \<triangleleft> update x k \<subseteq> g"
    proof -
      fix k
      have b: "p1 j k \<triangleleft> update x k \<subseteq> (p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> update x k"
        unfolding p1_def 
        by (metis domain_restrict_p_mono Int_Collect_mono Int_absorb inf.orderI)
      show "p1 j k \<triangleleft> update x k \<subseteq> g"
        using assm_g b by blast
    qed

    have proviso_q: "\<And>k. p1 j k \<triangleleft> update x k \<subseteq> qj j"
    proof -
      fix k
      have p1_contrib: "p1 j k \<triangleleft> update x k \<subseteq> {(\<sigma>,\<sigma>'). j \<succeq> k \<and> k \<succeq> eval e \<sigma>}"
      proof -
        have b: "{\<sigma>. j \<succeq> k \<and> k \<succeq> eval e \<sigma>} \<triangleleft> update x k \<subseteq> 
                  {(\<sigma>,\<sigma>'). j \<succeq> k \<and> k \<succeq> eval e \<sigma>}"
          by (simp add: restrict_domain_def) 
        show ?thesis using b p1_def domain_restrict_twice domain_restrict_remove
          by blast 
      qed
      have decr_e_contrib: "p1 j k \<triangleleft> update x k \<subseteq> {(\<sigma>,\<sigma>'). eval e \<sigma> \<succeq> eval e \<sigma>'}"
      proof -
        have c: "p \<triangleleft> update x k \<subseteq> {(\<sigma>,\<sigma>'). eval e \<sigma> \<succeq> eval e \<sigma>'}"                    
          using update_def decr_e_def id_dec domain_restrict_q_mono range_restrict_remove
          by (metis refine_trans)
        show ?thesis using p1_def c domain_restrict_p_mono inf.cobounded1 by blast
      qed
      have update_contrib: "p1 j k \<triangleleft> update x k \<subseteq> {(\<sigma>,\<sigma>'). get_var x \<sigma>' = k}"
      proof -
        have d: "update x k \<subseteq> {(\<sigma>,\<sigma>'). get_var x \<sigma>' = k}"
          using update_def range_restricts_contains id_bar_def var_eq_def 
          by (metis (no_types, lifting))  
        show ?thesis using d domain_restrict_remove by blast
      qed
      have combine: "p1 j k \<triangleleft> update x k \<subseteq> 
          {(\<sigma>,\<sigma>'). j \<succeq> k \<and> k \<succeq> eval e \<sigma> \<and> eval e \<sigma> \<succeq> eval e \<sigma>' \<and> get_var x \<sigma>' = k}"
          (is "_ \<ge> ?rhs")
        using p1_contrib decr_e_contrib update_contrib by auto
      have in_qj: "?rhs \<subseteq> qj j" 
      proof -
        have a: "\<And>\<sigma> \<sigma>'. j \<succeq> k \<and> k \<succeq> eval e \<sigma> \<and> eval e \<sigma> \<succeq> eval e \<sigma>' \<and> 
            get_var x \<sigma>' = k \<longrightarrow> j \<succeq> get_var x \<sigma>' \<and> get_var x \<sigma>' \<succeq> eval e \<sigma>'"
          using trans_gte transpD transpE by metis 
        show ?thesis using qj_def combine a by blast 
      qed
      show "p1 j k \<triangleleft> update x k \<subseteq> qj j"
        using combine in_qj by simp 
    qed

    have proviso_g_q: "\<And>k. p1 j k \<triangleleft> update x k \<subseteq> g \<inter> qj j"
      using proviso_g proviso_q by simp 

    have a: "rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> expr_eq e j\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> \<ge>
              rely r \<iinter> guar g \<iinter> \<lbrace>px j\<rbrace>; x:\<^sub>f\<lparr>qj j\<rparr>"  (is "_ \<ge> ?rhs")
    proof -
      have with_frame: "\<lbrace>p \<inter> expr_eq e j\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> \<ge> 
                          \<lbrace>p \<inter> {\<sigma>. j \<succeq> eval e \<sigma>}\<rbrace>; x:\<^sub>f\<lparr>qj j\<rparr>"
      proof -
        have a: "\<lbrace>p \<inter> expr_eq e j\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> = 
                  guar(id_bar{|x|}) \<iinter> \<lbrace>p \<inter> expr_eq e j\<rbrace>; \<lparr>q\<rparr>"
          by (simp add: conj.assert_distrib var_frame_expand) 
        have b: "\<dots> \<ge> guar(id_bar{|x|}) \<iinter> \<lbrace>p \<inter> {\<sigma>. j \<succeq> eval e \<sigma>}\<rbrace>; \<lparr>qj j\<rparr>" 
                (is "_ \<ge> ?rhs")
        proof -
          have within_j: "\<lbrace>p \<inter> expr_eq e j\<rbrace>; \<lparr>q\<rparr> \<ge> \<lbrace>p \<inter> {\<sigma>. j \<succeq> eval e \<sigma>}\<rbrace>; \<lparr>qj j\<rparr>"
          proof -
            have a: "\<lbrace>p \<inter> expr_eq e j\<rbrace>; \<lparr>q\<rparr> \<ge> \<lbrace>p \<inter> expr_eq e j\<rbrace>; \<lparr>qj j\<rparr>"
              using strengthen spec_strengthen_under_pre by force 
            have b: "p \<inter> expr_eq e j \<subseteq> p \<inter> {\<sigma>. j \<succeq> eval e \<sigma>}"
              using expr_eq_def weaken_to_gte using refl_gte by fastforce
            show "\<lbrace>p \<inter> expr_eq e j\<rbrace>; \<lparr>q\<rparr> \<ge> \<lbrace>p \<inter> {\<sigma>. j \<succeq> eval e \<sigma>}\<rbrace>; \<lparr>qj j\<rparr>"
              using a b assert_iso by (meson dual_order.trans seq_mono_left)
          qed
          show ?thesis using within_j conj.sync_mono_right by presburger
        qed
        have c: "?rhs = \<lbrace>p \<inter> {\<sigma>. j \<succeq> eval e \<sigma>}\<rbrace>; x:\<^sub>f\<lparr>qj j\<rparr>"
          using conj.assert_distrib var_frame_expand by auto
        show ?thesis using a b c by fastforce
      qed 
      show ?thesis using with_frame px_def  by (simp add: conj.sync_mono_right)
    qed
    have b: "?rhs \<ge> x ::= e"  (is "_ \<ge> ?rhs")
      using rely_guar_assign refl_g single_reference_e establish_p1 stable_p1 tolerates_q
        proviso_g_q by blast
    show "rely r \<iinter> guar g \<iinter> (\<lbrace>p \<inter> expr_eq e j\<rbrace>; x:\<^sub>f\<lparr>q\<rparr>) \<ge> x ::= e"
      using a b refine_trans by blast
  qed

  text \<open>Main proof\<close>
  have ma: "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> =
           (\<Squnion>j. \<tau>(expr_eq e j);(rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr>))"
    using let_j_e NONDET_seq_distrib seq_nil_left by metis 
  have mb: "\<dots> \<ge> (\<Squnion>j::'v. \<tau>(expr_eq e j); x ::= e)"  (is "_ \<ge> ?rhs")
  proof -
    have mba: "\<And>j. \<tau>(expr_eq e j);(rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr>) \<ge> 
                     \<tau>(expr_eq e j); x ::= e"
    proof -
      fix j
      have a: "\<tau>(expr_eq e j);(rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr>) \<ge> 
               \<tau>(expr_eq e j);\<lbrace>expr_eq e j\<rbrace>;(rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr>)" 
              (is "_ \<ge> ?rhs")
        by (simp add: test_seq_assert)
      have b: "?rhs \<ge> \<tau>(expr_eq e j);\<lbrace>expr_eq e j\<rbrace>;
                      (rely r \<iinter> guar g \<iinter> (\<lbrace>expr_eq e j\<rbrace>;\<lbrace>p\<rbrace>); x:\<^sub>f\<lparr>q\<rparr>)" (is "_ \<ge> ?rhs")
        by (metis assert_remove seq_assoc test_conj_distrib test_seq_assert)
      have c: "?rhs \<ge> \<tau>(expr_eq e j);(rely r \<iinter> guar g \<iinter> (\<lbrace>p \<inter> expr_eq e j\<rbrace>; x:\<^sub>f\<lparr>q\<rparr>))"
              (is "_ \<ge> ?rhs")
        using test_seq_assert assert_seq_assert by (simp add: inf.commute)
      have d: "?rhs \<ge>  \<tau>(expr_eq e j); x ::= e"
        using body by (simp add: seq_mono)
      show "\<tau>(expr_eq e j);(rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr>) \<ge>  \<tau>(expr_eq e j); x ::= e"
        using a b c d by force
    qed
    show ?thesis using mba by (simp add: NONDET_mono_quant)
  qed
  have mc: "\<dots> \<ge> x ::= e"
    using mb let_j_e by (metis NONDET_seq_distrib seq_nil_left)
  show ?thesis 
    using ma mc q_def by force
qed

end

end
