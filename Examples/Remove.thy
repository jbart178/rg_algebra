section \<open>Removing an element from a set\<close>

theory Remove imports 
  "../Programming/Programming_Constructs"

begin

datatype varname = w | i | pw | nw

datatype Value = bool_val (the_Bool:bool) | nat_val (the_Nat:nat) | set_val (the_Set:"nat fset")

instantiation Value :: has_booleans
begin
  definition true_Value :: "Value" where "true_Value = bool_val True"
  definition false_Value :: "Value" where "false_Value = bool_val False"

  instance proof
    show "(has_booleans_class.true::Value) \<noteq> has_booleans_class.false"
      by (simp add: true_Value_def false_Value_def)
  qed
end

type_synonym state = "varname \<Rightarrow> Value"

locale remove_pre = state_relations + (*atomic_specification + while_loop + intro_par_big + assignments + *)
  constrains seq :: "'a::refinement_lattice \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a::refinement_lattice"
  constrains test :: "state set \<Rightarrow> 'a"
  constrains par :: "'a::refinement_lattice \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a::refinement_lattice"
  constrains conj :: "'a::refinement_lattice \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a::refinement_lattice"
  constrains pgm :: "state rel \<Rightarrow> 'a"
  constrains env :: "state rel \<Rightarrow> 'a"
  constrains get_var :: "varname \<Rightarrow> state \<Rightarrow> Value"
  constrains set_var :: "varname \<Rightarrow> Value \<Rightarrow> state \<Rightarrow> state"
  constrains var_eq :: "varname \<Rightarrow> Value \<Rightarrow> (state set)"
  constrains assign :: "varname \<Rightarrow> (state, Value) expr \<Rightarrow> 'a" 
  constrains atomic_spec :: "state set \<Rightarrow> state rel \<Rightarrow> 'a"
  assumes get_var: "get_var x \<sigma> = \<sigma> x"
  assumes set_var: "set_var x v \<sigma> = \<sigma>(x := v)"
begin

sublocale programming_constructs seq test par conj pgm env set_var get_var
           (* lib lib_first lib_last lib_bool_sets bool_first_sets bool_last_sets 
            lib_bool bool_first bool_last *)
proof
qed

definition member_val :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "\<in>\<^sub>v" 50) where
  "member_val x s =  bool_val(the_Nat x |\<in>| the_Set s)"
definition subtract_set :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "-\<^sub>s" 65) where
  "subtract_set s1 s2 = set_val(the_Set s1 |-| the_Set s2)"
definition remove_val :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "-\<^sub>v" 65) where
  "remove_val s v = set_val(the_Set s |-| {|the_Nat v|})"
definition not_member_rel :: "Value \<Rightarrow> Value \<Rightarrow> bool" (infix "\<notin>\<^sub>r" 50) where
  "not_member_rel x s = (the_Nat x |\<notin>| the_Set s)"
definition subset_rel :: "Value \<Rightarrow> Value \<Rightarrow> bool" (infix "\<subset>\<^sub>r" 50) where
  "subset_rel s1 s2 = (is_set_val s1 \<and> is_set_val s2 \<and> the_Set s1 |\<subset>| the_Set s2)"
definition subseteq_rel :: "Value \<Rightarrow> Value \<Rightarrow> bool" (infix "\<subseteq>\<^sub>r" 50) where
  "subseteq_rel s1 s2 = (s1 = s2 \<or> s1 \<subset>\<^sub>r s2)"

lemma subseteq_subset: "s1 \<subseteq>\<^sub>r s2 \<and> s2 \<subset>\<^sub>r s3 \<Longrightarrow> s1 \<subset>\<^sub>r s3" 
  unfolding subset_rel_def subseteq_rel_def by blast

definition vw where "vw = (\<lambda>\<sigma>::state. the_Set(\<sigma> w))"
definition vi where "vi = (\<lambda>\<sigma>::state. the_Nat(\<sigma> i))"

definition expr_w where "expr_w = Variable(\<lambda>\<sigma>::state. \<sigma> w)"
definition expr_i where "expr_i = Variable(\<lambda>\<sigma>::state. \<sigma> i)"
definition expr_pw where "expr_pw = Variable(\<lambda>\<sigma>::state. \<sigma> pw)"
definition variant where "variant = (\<lambda>\<sigma>::state. \<sigma>)"

definition N :: nat where "N = 32"
definition Word :: "nat \<Rightarrow> nat fset" where "Word n = Abs_fset {j::nat. j < n}"

text \<open>Specification defintions\<close>
(*definition p where "p = {\<sigma>::state. is_set_val(\<sigma> vw) \<and> is_nat_val(\<sigma> vi) \<and> w_val \<sigma> |\<subseteq>| Word N \<and> i \<sigma> |\<in>| Word N}"*)
definition p where "p = {\<sigma>::state. is_set_val(\<sigma> w) \<and> is_nat_val(\<sigma> i)}"
definition g where "g = {(\<sigma>::state,\<sigma>'). \<sigma>' w \<subseteq>\<^sub>r \<sigma> w \<and> \<sigma> w -\<^sub>s \<sigma>' w \<subseteq>\<^sub>r set_val{|vi \<sigma>|} }"
definition r where "r = {(\<sigma>::state,\<sigma>'). (is_set_val(\<sigma> w) \<longrightarrow> is_set_val(\<sigma>' w)) \<and> 
                          \<sigma>' w \<subseteq>\<^sub>r \<sigma> w \<and> \<sigma>' i = \<sigma> i \<and> \<sigma>' pw = \<sigma> pw \<and> \<sigma>' nw = \<sigma> nw}"
definition q where "q = {(\<sigma>::state,\<sigma>'). \<sigma>' i = \<sigma> i}"

text \<open>Implementation definitions\<close>
definition b where "b = BinaryOp (\<in>\<^sub>v) expr_i expr_w"
definition CAS_post where "CAS_post = {(\<sigma>,\<sigma>'). (\<sigma> w = \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> nw) \<and> (\<sigma> w \<noteq> \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> w)}"
definition CAS where "CAS = w:\<^sub>f\<langle>UNIV, CAS_post\<rangle>"
definition pw_minus_i where "pw_minus_i = BinaryOp (-\<^sub>v) expr_pw expr_i"
definition body where "body = (pw ::= expr_w ; nw ::= pw_minus_i ; CAS)"

text \<open>While loop auxilary definitions\<close>
definition b_t where "b_t = {\<sigma>::state. True}"
definition b_f where "b_f = {\<sigma>::state. \<sigma> i \<notin>\<^sub>r \<sigma> w}"
definition b_x where "b_x = b_f"
definition wfr where "wfr = {(x,y). x |\<subset>| y}"

text \<open>Body decomposition into sequential composition definitions\<close>
definition goal where "goal = (\<lambda>v::varname. {(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i \<and> is_set_val(\<sigma>' w) \<and> (\<sigma>' w \<subset>\<^sub>r \<sigma> v \<or> \<sigma>' i \<notin>\<^sub>r \<sigma>' w)})"
definition nw_pre where "nw_pre = p \<inter> {\<sigma> . \<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> is_set_val(\<sigma> pw)}"
definition pw_post where "pw_post = {(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i \<and> \<sigma>' pw \<subseteq>\<^sub>r \<sigma> w} \<triangleright> nw_pre"
definition w_pre where "w_pre = nw_pre \<inter> {\<sigma>. \<sigma> nw = \<sigma> pw -\<^sub>v \<sigma> i}"
definition nw_post where "nw_post = {(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i \<and> \<sigma>' pw = \<sigma> pw} \<triangleright> w_pre"

lemma seq_mono_rightx: 
  assumes "c \<ge> c1 ; c2"
  assumes "c2 \<ge> d1 ; d2"
  shows "c \<ge> c1 ; d1 ; d2"
  by (metis assms(1) assms(2) seq_assoc dual_order.trans seq_mono_right)

lemma Example16_17:
  "\<lbrace>p\<rbrace> ; {|nw,pw,w|}:\<^sub>s\<lparr>goal w\<rparr> \<ge> \<lbrace>p\<rbrace> ; pw:\<^sub>f\<lparr>pw_post\<rparr> ; \<lbrace>nw_pre\<rbrace> ; nw:\<^sub>f\<lparr>nw_post\<rparr> ; \<lbrace>w_pre\<rbrace> ; w:\<^sub>f\<lparr>goal pw\<rparr>"
proof -
  have a: "\<lbrace>p\<rbrace> ; {|nw,pw,w|}:\<^sub>s\<lparr>goal w\<rparr> \<ge> \<lbrace>p\<rbrace> ; {|nw,pw,w|}:\<^sub>s\<lparr>pw_post\<rparr> ; \<lbrace>nw_pre\<rbrace> ; {|nw,pw,w|}:\<^sub>s\<lparr>goal pw\<rparr>"
    (is "_ \<ge> ?rhs")
  proof -
    have pw_post_restrict_p_nw_pre: "pw_post \<triangleright> nw_pre = pw_post"
      unfolding restrict_range_def pw_post_def p_def nw_pre_def using range_restrict_twice  
      by fastforce
    have mid: "p \<triangleleft> ((pw_post \<triangleright> nw_pre) O goal pw) = p \<triangleleft> (pw_post O goal pw)"
      by (simp add: pw_post_restrict_p_nw_pre) 
    have asm: "\<dots> \<subseteq> goal w" 
      unfolding p_def pw_post_def goal_def
      using pw_post_restrict_p_nw_pre domain_restrict_remove 
      by (smt (z3) IntE case_prod_conv mem_Collect_eq relcompE restrict_domain_def
          restrict_range_def subsetI subseteq_rel_def subseteq_subset)      
    show ?thesis using spec_seq_introduce_framed pw_post_restrict_p_nw_pre asm 
      by (metis (no_types, lifting))
  qed
  have a_frame1: "?rhs \<ge> \<lbrace>p\<rbrace> ; pw:\<^sub>f\<lparr>pw_post\<rparr> ; \<lbrace>nw_pre\<rbrace> ; {|nw,pw,w|}:\<^sub>s\<lparr>goal pw\<rparr>"
      (is "_ \<ge> ?rhs")
    using restrict_frame by (simp add: seq_mono var_frame_def) 
  have a_frame2: "?rhs \<ge> \<lbrace>p\<rbrace> ; pw:\<^sub>f\<lparr>pw_post\<rparr> ; \<lbrace>nw_pre\<rbrace> ; {|nw,w|}:\<^sub>s\<lparr>goal pw\<rparr>"
    using restrict_frame seq_mono by auto
  have a_done: "\<lbrace>p\<rbrace> ; {|nw,pw,w|}:\<^sub>s\<lparr>goal w\<rparr> \<ge> (\<lbrace>p\<rbrace> ; pw:\<^sub>f\<lparr>pw_post\<rparr>) ; (\<lbrace>nw_pre\<rbrace> ; {|nw,w|}:\<^sub>s\<lparr>goal pw\<rparr>)"
    using a a_frame1 a_frame2 seq_assoc by fastforce
  have b: "\<lbrace>nw_pre\<rbrace> ; {|nw,w|}:\<^sub>s\<lparr>goal pw\<rparr> \<ge> 
            \<lbrace>nw_pre\<rbrace> ; {|nw,w|}:\<^sub>s\<lparr>nw_post\<rparr> ; \<lbrace>w_pre\<rbrace> ;{|nw,w|}:\<^sub>s\<lparr>goal pw\<rparr>"
        (is "_ \<ge> ?rhs")
  proof -
    have pw_post_restrict_w_pre: "nw_post \<triangleright> w_pre = nw_post"
      using range_restrict_twice by (simp add: nw_post_def restrict_range_def)
    have asm: "nw_pre \<triangleleft> ((nw_post \<triangleright> w_pre) O goal pw) \<subseteq> goal pw"
    proof - 
      have asma: "nw_pre \<triangleleft> ((nw_post \<triangleright> w_pre) O goal pw) \<subseteq> nw_post O goal pw"
        using pw_post_restrict_w_pre domain_restrict_remove by fastforce   
      have asmb: "\<dots> \<subseteq> goal pw" 
        unfolding nw_post_def goal_def w_pre_def restrict_range_def by force
      show ?thesis using asma asmb goal_def by auto 
    qed
    have almost: "\<lbrace>nw_pre\<rbrace> ; {|nw,w|}:\<^sub>s\<lparr>goal pw\<rparr> \<ge>
                  \<lbrace>nw_pre\<rbrace> ; {|nw,w|}:\<^sub>s\<lparr>nw_post \<triangleright> w_pre\<rparr> ; \<lbrace>w_pre\<rbrace> ;{|nw,w|}:\<^sub>s\<lparr>goal pw\<rparr>"
      using asm spec_seq_introduce_framed by presburger 
    show ?thesis using pw_post_restrict_w_pre almost by presburger  
  qed
  have b_frame1: "?rhs \<ge> \<lbrace>nw_pre\<rbrace> ; nw:\<^sub>f\<lparr>nw_post\<rparr> ; \<lbrace>w_pre\<rbrace> ; {|nw,w|}:\<^sub>s\<lparr>goal pw\<rparr>"
      (is "_ \<ge> ?rhs")
    using restrict_frame seq_mono var_frame_def by auto  
  have b_frame2: "?rhs \<ge> \<lbrace>nw_pre\<rbrace> ; nw:\<^sub>f\<lparr>nw_post\<rparr> ; \<lbrace>w_pre\<rbrace> ; w:\<^sub>f\<lparr>goal pw\<rparr>"
    using restrict_frame var_frame_def seq_mono by force 
  have b_done: "\<lbrace>nw_pre\<rbrace> ; {|nw,w|}:\<^sub>s\<lparr>goal pw\<rparr> \<ge> \<lbrace>nw_pre\<rbrace> ; nw:\<^sub>f\<lparr>nw_post\<rparr> ; \<lbrace>w_pre\<rbrace> ; w:\<^sub>f\<lparr>goal pw\<rparr>"
    using b b_frame1 b_frame2 by auto
  show ?thesis using seq_mono_right a_done b_done seq_assoc 
    using seq_mono_rightx by force
qed

lemma refl_gte: "reflp (\<subseteq>\<^sub>r)"  
    by (simp add: reflp_onI subseteq_rel_def) 

lemma trans_gte: "transp (\<subseteq>\<^sub>r)"
    by (smt (verit, ccfv_SIG) order_less_trans subset_rel_def subseteq_rel_def transp_onI) 

lemma empty_sub: "\<And>\<sigma> \<sigma>'. \<sigma> w = \<sigma>' w \<Longrightarrow>  \<sigma> w -\<^sub>s \<sigma>' w = set_val{||}"
  by (simp add: subtract_set_def) 

lemma refl_g: "refl g"
proof -
  have a: "\<And>\<sigma>. \<sigma> w \<subseteq>\<^sub>r \<sigma> w \<and> \<sigma> w -\<^sub>s \<sigma> w \<subseteq>\<^sub>r set_val{|vi \<sigma>|}" 
    using empty_sub subset_rel_def subseteq_rel_def by auto 
  show ?thesis using a by (simp add: g_def reflI)   
qed

lemma stable_p: "stable p r"
    unfolding stable_def p_def r_def by force

lemma assign_pw: 
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; pw:\<^sub>f\<lparr>pw_post\<rparr> \<ge> pw ::= expr_w"
proof -
  let ?qq = "{(\<sigma>,\<sigma>'). \<sigma>' w \<subseteq>\<^sub>r \<sigma>' pw \<and> \<sigma>' pw \<subseteq>\<^sub>r \<sigma> w}"
  have stable_pw: "r \<subseteq> id pw" 
    unfolding r_def get_var local.id_def r_def by fastforce 
  have single_reference_e: "single_reference expr_w r" 
    by (simp add: expr_w_def)
  have assm_g: "\<And>k. (p \<inter> {\<sigma>. eval expr_w \<sigma> \<subseteq>\<^sub>r k}) \<triangleleft> update pw k \<subseteq> g"
  proof -
    fix k
    have a: "(p \<inter> {\<sigma>. eval expr_w \<sigma> \<subseteq>\<^sub>r k}) \<triangleleft> update pw k \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' w = \<sigma> w}"
    proof -
      have aa: "update pw k \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' w = \<sigma> w}" 
        unfolding update_def id_bar_def var_eq_def get_var 
        by (simp add: range_restricts_contains) 
      show ?thesis using aa domain_restrict_remove by blast
    qed
    show "(p \<inter> {\<sigma>. eval expr_w \<sigma> \<subseteq>\<^sub>r k}) \<triangleleft> update pw k \<subseteq> g"
      using empty_sub 
      by (smt (verit, del_insts) Collect_split_mono_strong Value.disc(9) Value.sel(3) a g_def
          inf.strict_order_iff inf_bot_left subset_rel_def subseteq_rel_def)  
  qed 
  have r_decr: "r \<subseteq> {(\<sigma>,\<sigma>'). (eval expr_w \<sigma>') \<subseteq>\<^sub>r (eval expr_w \<sigma>)}" (is "_ \<subseteq> ?decr_w")
    using r_def subset_iff expr_w_def  
    by (smt (verit, del_insts) Collect_mono case_prodD case_prodI2 eval.simps(2))
  have id_dec: "p \<triangleleft> id_bar {|pw|} \<subseteq> ?decr_w" 
  proof -
    have a: "id_bar {|pw|} \<subseteq> ?decr_w" 
      unfolding id_bar_def get_var using eval.elims 
      by (smt (verit, ccfv_threshold) Ball_Collect case_prodD case_prodI2 eval.simps(2) expr_w_def
          fsingletonE mem_Collect_eq subseteq_rel_def varname.distinct(3)) 
    show ?thesis using a 
      using domain_restrict_remove by blast 
  qed
  have maintain_inv: "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; pw:\<^sub>f\<lparr>pw_post\<rparr> \<ge> rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; pw:\<^sub>f\<lparr>?qq\<rparr>" 
  proof -
    have strengthen: "p \<triangleleft> ?qq \<inter> id i \<subseteq> pw_post" 
    proof -
      have a: "p \<triangleleft> id i \<subseteq> {(\<sigma>,\<sigma>'). is_nat_val(\<sigma>' i)}"
        unfolding p_def id_def get_var by (metis (mono_tags, lifting) domain_restricts_contains) 
      have b: "p \<triangleleft> ?qq \<subseteq> {(\<sigma>,\<sigma>'). is_set_val(\<sigma>' w)}" 
        by (metis (no_types, lifting) domain_restricts_contains p_def subset_rel_def subseteq_rel_def) 
      have c: "p \<triangleleft> ?qq \<inter> id i \<subseteq> range_restriction p" 
        unfolding p_def using a b 
        by (smt (verit, del_insts) IntE case_prodD case_prodI2 get_var inf.orderE local.id_def
            mem_Collect_eq p_def restrict_domain_def subsetI)
      have d: "p \<triangleleft> ?qq \<inter> id i \<subseteq> {(\<sigma>,\<sigma>'). is_set_val(\<sigma>' pw)}" 
        by (metis (no_types, lifting) domain_restricts_contains inf.coboundedI1 p_def subset_rel_def
            subseteq_rel_def) 
      have e: "p \<triangleleft> ?qq \<inter> id i \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' w \<subseteq>\<^sub>r \<sigma>' pw}"
        using domain_restrict_remove by blast
      have f: "p \<triangleleft> ?qq \<inter> id i \<subseteq> range_restriction nw_pre"
        unfolding nw_pre_def using c d e by blast
      have g: "p \<triangleleft> ?qq \<inter> id i \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i}"
        unfolding id_def get_var using domain_restrict_remove by force 
      have h: "p \<triangleleft> ?qq \<inter> id i \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' pw \<subseteq>\<^sub>r \<sigma> w}" 
        using domain_restrict_remove by blast 
      show ?thesis unfolding restrict_range_def pw_post_def using f g h 
        by auto 
    qed
    have rely_nochange: "r \<subseteq> id i"
      unfolding r_def id_def get_var by force 
    have b: "rely r \<iinter> pw:\<^sub>f\<lparr>pw_post\<rparr> \<ge> rely r \<iinter> pw:\<^sub>f\<lparr>p \<triangleleft> ?qq\<rparr>" (is "_ \<ge> ?rhs")
      using strengthen rely_nochange spec_strengthen_with_trading by blast
    have c: "rely r \<iinter> \<lbrace>p\<rbrace>; pw:\<^sub>f\<lparr>pw_post\<rparr> \<ge> rely r \<iinter> \<lbrace>p\<rbrace>; pw:\<^sub>f\<lparr>p \<triangleleft> ?qq\<rparr>"
      using b using refine_within_rely_right by blast 
    show ?thesis using c 
      using assert_restricts_spec conj.assert_distrib var_frame_expand 
      using conj.comm.left_commute conj.sync_mono local.conj_assoc by force  
  qed
  have assign_mono: "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; pw:\<^sub>f\<lparr>?qq\<rparr> \<ge> pw ::= expr_w"
    apply (rule rely_guar_assignment_monotonic)
    using refl_g apply blast 
    using stable_p apply blast 
    using stable_pw apply blast 
    using single_reference_e apply blast
    using refl_gte  using reflp_on_def apply blast
    using trans_gte using transp_def apply blast
    using assm_g apply presburger 
    using r_decr apply force
    using id_dec apply force 
    by (simp add: expr_w_def get_var)
  have almost: "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace>; pw:\<^sub>f\<lparr>pw_post\<rparr> \<ge> pw ::= expr_w"
    using maintain_inv assign_mono dual_order.trans by blast 
  show ?thesis using almost by blast 
qed

lemma stable_nw_pre: "stable nw_pre r"
proof -
  have stable_rest: "stable {\<sigma> . \<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> is_set_val(\<sigma> pw)} r"
    unfolding stable_def r_def 
    by (smt (verit) Ball_Collect ImageE case_prodD mem_Collect_eq subseteq_rel_def subseteq_subset)
  show ?thesis unfolding nw_pre_def using stable_inter stable_p stable_rest 
    by auto 
qed    

lemma stable_w_pre : "stable w_pre r"
proof -
  have stable_nw: "stable {\<sigma>. \<sigma> nw = \<sigma> pw -\<^sub>v \<sigma> i} r"
    unfolding stable_def r_def by force 
  show ?thesis unfolding w_pre_def using stable_inter stable_p stable_nw_pre stable_nw 
    by blast
qed

lemma assign_nw:
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>nw_pre\<rbrace> ; nw:\<^sub>f\<lparr>nw_post\<rparr> \<ge> nw ::= pw_minus_i"
proof -
  have single_reference_e: "single_reference pw_minus_i r" 
    by (simp add: estable_def r_def expr_i_def expr_pw_def pw_minus_i_def)  
  have estable_e: "estable pw_minus_i r" 
    by (simp add: estable_def r_def expr_i_def expr_pw_def pw_minus_i_def)
  have rq: "nw_pre \<triangleleft> (r O nw_post) \<subseteq> nw_post"
    unfolding nw_post_def r_def using domain_restrict_remove relcompE restrict_range_def subset_eq 
    by (smt (verit) Int_iff case_prodD case_prodI mem_Collect_eq)
  have qr: "nw_pre \<triangleleft> (nw_post O r) \<subseteq> nw_post"
    unfolding nw_pre_def nw_post_def r_def w_pre_def p_def 
    by (smt (verit, del_insts) Int_iff case_prodD case_prodI mem_Collect_eq relcompE
        restrict_domain_def restrict_range_def subset_eq subseteq_rel_def subseteq_subset) 
  have tolerates_q: "tolerates_interference nw_pre nw_post r"
    using stable_nw_pre rq qr tolerates_interference_def by blast
  have req_g: "\<And>k. (nw_pre \<inter> expr_eq (pw_minus_i) k) \<triangleleft> update nw k \<subseteq> g"  
  proof -
    fix k
    have aa: "update nw k \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' w = \<sigma> w}" 
      unfolding update_def id_bar_def var_eq_def get_var
      by (simp add: range_restricts_contains) 
    show "(nw_pre \<inter> expr_eq (pw_minus_i) k) \<triangleleft> update nw k \<subseteq> g"
      unfolding g_def subset_rel_def subseteq_rel_def using aa domain_restrict_remove empty_sub subset_trans
      by (smt (verit, del_insts) Collect_split_mono_strong Value.disc(9) Value.sel(3)
          fsubset_finsertI order_le_neq_trans)  
  qed
  have req_q: "\<And>k. (nw_pre \<inter> expr_eq (pw_minus_i) k) \<triangleleft> update nw k \<subseteq> nw_post"
  proof -
    fix k
    have post_p: "p \<triangleleft> id_bar{|nw|} \<subseteq> range_restriction p"
      unfolding w_pre_def nw_pre_def p_def  
      by (smt (verit) domain_restricts_contains fsingletonE get_var id_bar_def mem_Collect_eq
          varname.distinct(5) varname.distinct(9)) 
    have post_nw_prex: "{\<sigma> . \<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> is_set_val(\<sigma> pw)} \<triangleleft> id_bar{|nw|} \<subseteq> 
                        range_restriction {\<sigma> . \<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> is_set_val(\<sigma> pw)}" 
      by (smt (verit, best) domain_restricts_contains fsingletonE get_var id_bar_def mem_Collect_eq
          varname.distinct(11) varname.distinct(5))

    have post_nw_pre: "nw_pre \<triangleleft> id_bar{|nw|} \<subseteq> range_restriction (nw_pre)"
      unfolding nw_pre_def using post_p post_nw_prex 
      by (smt (verit, ccfv_SIG) Ball_Collect Int_iff case_prodI2 case_prod_conv mem_Collect_eq
          restrict_domain_def) 
    have a: "(nw_pre \<inter> expr_eq (pw_minus_i) k) \<triangleleft> update nw k \<subseteq> range_restriction (nw_pre)" 
      by (smt (verit, best) domain_restrict_q_mono domain_restrict_remove domain_restrict_twice
          order_trans post_nw_pre update_nochange)
    have m: "(nw_pre \<inter> expr_eq pw_minus_i k) \<triangleleft> update nw k \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' nw = \<sigma>' pw -\<^sub>v \<sigma>' i}"
    proof -
      have la: "\<And>\<sigma>. eval pw_minus_i \<sigma> = \<sigma> pw -\<^sub>v \<sigma> i" 
        by (simp add: remove_val_def expr_i_def expr_pw_def pw_minus_i_def) 
      have lb: "{\<sigma>. \<sigma> pw -\<^sub>v \<sigma> i = k} \<triangleleft> update nw k \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' nw = \<sigma> pw -\<^sub>v \<sigma> i}"
        using update_eq 
        by (smt (verit, del_insts) Ball_Collect IntE case_prodD case_prodI2 get_var mem_Collect_eq
            restrict_domain_def)
      have lc: "{\<sigma>. eval pw_minus_i \<sigma> = k} \<triangleleft> update nw k \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' nw =  \<sigma> pw -\<^sub>v \<sigma> i}"
        using la lb by presburger 
      have ld: "(expr_eq pw_minus_i k) \<triangleleft> update nw k \<subseteq> {(\<sigma>,\<sigma>') . \<sigma>' nw =  \<sigma> pw -\<^sub>v \<sigma> i}"
        using lc by (simp add: expr_eq_def) 
      have le: "(expr_eq pw_minus_i k) \<triangleleft> update nw k \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' pw = \<sigma> pw \<and> \<sigma>' i = \<sigma> i}"
        unfolding update_def id_bar_def 
        by (smt (verit) Ball_Collect case_prodD case_prodI2 domain_restrict_remove fsingletonE
            get_var le_inf_iff restrict_range_def varname.distinct(11) varname.distinct(9))
      have lf: "(expr_eq pw_minus_i k) \<triangleleft> update nw k \<subseteq> {(\<sigma>,\<sigma>') . \<sigma>' nw =  \<sigma>' pw -\<^sub>v \<sigma>' i}"
          using ld le by (smt (verit) Ball_Collect case_prodD case_prodI2)
      show ?thesis using lf using domain_restrict_remove domain_restrict_twice by blast 
    qed
    have b: "(nw_pre \<inter> expr_eq pw_minus_i k) \<triangleleft> update nw k \<subseteq> range_restriction w_pre"
      unfolding w_pre_def using range_restrict_inter a m 
      by (smt (verit, ccfv_threshold) Ball_Collect Int_iff case_prodD case_prodI2 mem_Collect_eq)
    have a: "(nw_pre \<inter> expr_eq pw_minus_i k) \<triangleleft> update nw k \<subseteq> (nw_pre \<inter> expr_eq pw_minus_i k) \<triangleleft> update nw k \<triangleright> w_pre"
      by (simp add: b restrict_range_def) 
    have b: "update nw k \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i \<and> \<sigma>' pw = \<sigma> pw}"
      unfolding update_def id_bar_def get_var 
      by (metis (mono_tags, lifting) Collect_split_mono_strong fsingletonE range_restrict_remove
          varname.distinct(11) varname.distinct(9))
    show "(nw_pre \<inter> expr_eq (pw_minus_i) k) \<triangleleft> update nw k \<subseteq> nw_post"
      using a b
      by (metis (no_types, lifting) domain_restrict_remove nw_post_def range_restrict_q_mono refine_trans)  
  qed
  show ?thesis 
    apply (rule local_expr_assign)
    using refl_g apply blast
    using single_reference_e apply auto
    using estable_e apply (simp add: r_def stable_expression_variable expr_i_def)
    using tolerates_q apply auto
    using req_g estable_e apply force 
    using req_q by blast
qed                     

lemma intro_CAS:
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>w_pre\<rbrace> ; w:\<^sub>f\<lparr>goal pw\<rparr> \<ge> CAS"
proof -
  have refl_id_bar_g: "refl(id_bar{|w|} \<inter> g)" using refl_g 
    by (metis id_bar_refl inf_top_right refl_on_Int)
  let ?qnw_w_post = "{(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i \<and> is_set_val(\<sigma>' w) \<and> (\<sigma>' w \<subset>\<^sub>r \<sigma> pw \<or> \<sigma> i \<notin>\<^sub>r \<sigma>' w)}"
  have rq: "w_pre \<triangleleft> (r O ?qnw_w_post) \<subseteq> ?qnw_w_post"
  proof - 
    have a: "r O ?qnw_w_post \<subseteq> ?qnw_w_post"
      unfolding r_def by force 
    show ?thesis using a 
      by (meson domain_restrict_remove dual_order.trans)
  qed
  have qr: "w_pre \<triangleleft> (?qnw_w_post O r) \<subseteq> ?qnw_w_post"
  proof -
    have a: "?qnw_w_post O {(\<sigma>,\<sigma>'). \<sigma>' w \<subseteq>\<^sub>r \<sigma> w \<and> \<sigma>' i = \<sigma> i \<and> \<sigma>' pw = \<sigma> pw} \<subseteq> ?qnw_w_post" 
      unfolding r_def 
      by (smt (z3) BNF_Def.Collect_case_prodD case_prodI mem_Collect_eq not_member_rel_def pfsubsetD
          prod.sel(1) prod.sel(2) relcompEpair subrelI subset_rel_def subseteq_rel_def subseteq_subset)
    have b: "?qnw_w_post O r \<subseteq> ?qnw_w_post"
      unfolding r_def using a by blast 
    show ?thesis using b domain_restrict_remove 
      by blast 
  qed
  have tolerates: "tolerates_interference w_pre ?qnw_w_post r"
    unfolding tolerates_interference_def stable_w_pre rq qr 
    using qr rq stable_w_pre by blast
  have a: "rely r \<iinter> guar g \<iinter> \<lbrace>w_pre\<rbrace> ; w:\<^sub>f\<lparr>goal pw\<rparr> \<ge> 
        rely r \<iinter> guar g \<iinter> \<lbrace>w_pre\<rbrace> ; w:\<^sub>f\<lparr>?qnw_w_post\<rparr>"
          (is "_ \<ge> ?rhs")  
  proof -
    have aa: "?qnw_w_post \<subseteq> goal pw"
      unfolding goal_def by force 
    show ?thesis using aa  spec_strengthen 
      by (simp add: conj.sync_mono_right frame_mono seq_mono) 
  qed
  have b: "?rhs \<ge> rely r \<iinter> \<langle>w_pre, id_bar{|w|} \<inter> g \<inter> ?qnw_w_post\<rangle>"
          (is "_ \<ge> ?rhs")
    using atomic_spec_introduce_framed refl_g tolerates by blast 
  have c: "?rhs \<ge> rely r \<iinter> \<langle>w_pre , id_bar{|w|} \<inter> g \<inter> ?qnw_w_post\<rangle>"
          (is "_ \<ge> ?rhs")
    using atomic_spec_weaken_pre  
    by (simp add: conj.sync_mono_right p_def w_pre_def) 
  have d: "?rhs \<ge> rely r \<iinter> \<langle>w_pre, id_bar{|w|} \<inter> CAS_post\<rangle>"
          (is "_ \<ge> ?rhs")
  proof -
    have strengthen: "w_pre \<triangleleft> id_bar{|w|} \<inter> CAS_post \<subseteq> id_bar{|w|} \<inter> g \<inter> ?qnw_w_post"
    proof - 
      have show_g: "\<And>\<sigma> \<sigma>'. is_nat_val(\<sigma> i) \<and> \<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> \<sigma> nw = \<sigma> pw -\<^sub>v \<sigma> i \<and> is_set_val(\<sigma> pw) \<and> (\<sigma> w = \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> nw) \<and> (\<sigma> w \<noteq> \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> w)
                     \<longrightarrow> \<sigma>' w \<subseteq>\<^sub>r \<sigma> w \<and> \<sigma> w -\<^sub>s \<sigma>' w \<subseteq>\<^sub>r set_val{|vi \<sigma>|}" 
      proof -
        fix \<sigma> \<sigma>'
        show "is_nat_val(\<sigma> i) \<and> \<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> \<sigma> nw = \<sigma> pw -\<^sub>v \<sigma> i \<and> is_set_val(\<sigma> pw) \<and> (\<sigma> w = \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> nw) \<and> (\<sigma> w \<noteq> \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> w)
                     \<longrightarrow> \<sigma>' w \<subseteq>\<^sub>r \<sigma> w \<and> \<sigma> w -\<^sub>s \<sigma>' w \<subseteq>\<^sub>r set_val{|vi \<sigma>|}"
        proof (cases "\<sigma> w = \<sigma> pw")
          case True
          have ta: "\<And>nw pw i. nw = pw |-| {|i|} \<longrightarrow> nw |\<subseteq>| pw" 
            by fastforce 
          have tb: "\<And>w w' nw pw i. w \<subseteq>\<^sub>r pw \<and> nw = pw -\<^sub>v i \<and> w' = nw \<and> is_set_val(pw) \<and> is_nat_val i \<longrightarrow> w' \<subseteq>\<^sub>r pw" 
            using ta remove_val_def subset_rel_def subseteq_rel_def 
            by (metis Value.collapse(3) Value.disc(9) Value.sel(3) antisym_conv1) 
          have tc: "\<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> \<sigma> nw = \<sigma> pw -\<^sub>v \<sigma> i \<and> \<sigma>' w = \<sigma> nw \<and> is_set_val(\<sigma> pw) \<and> is_nat_val(\<sigma> i) \<longrightarrow> \<sigma>' w \<subseteq>\<^sub>r \<sigma> w"
            using tb True by force
          have td: "\<And>w w' pw i. w \<subseteq>\<^sub>r pw \<and> w' = pw -\<^sub>v i \<longrightarrow> w -\<^sub>s w' \<subseteq>\<^sub>r set_val{|the_Nat i|}" 
            using double_fminus remove_val_def subset_rel_def subseteq_rel_def subtract_set_def by auto  
          have te: "\<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> \<sigma>' w = \<sigma> pw -\<^sub>v \<sigma> i \<longrightarrow> \<sigma> w -\<^sub>s \<sigma>' w \<subseteq>\<^sub>r set_val{|vi \<sigma>|}" 
            using td vi_def by presburger
          then show ?thesis
            by (metis True tb) 
        next
          case False
          have fa: "is_set_val(\<sigma>' w) \<and> is_set_val(\<sigma> w) \<and> \<sigma>' w = \<sigma> w \<longrightarrow> \<sigma>' w \<subseteq>\<^sub>r \<sigma> w" 
            using subseteq_rel_def by blast  
          have fb: "\<sigma>' w = \<sigma> w \<longrightarrow>  \<sigma> w -\<^sub>s \<sigma>' w \<subseteq>\<^sub>r set_val{|vi \<sigma>|}" 
            using subset_rel_def subseteq_rel_def subtract_set_def by force 
          then show ?thesis using fa fb False 
            using subseteq_rel_def by auto 
        qed        
      qed
      have show_post: "\<And>\<sigma> \<sigma>'. is_nat_val(\<sigma> i) \<and> \<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> \<sigma> nw = \<sigma> pw -\<^sub>v \<sigma> i \<and> \<sigma>' i = \<sigma> i \<and> (\<sigma> w = \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> nw) \<and> (\<sigma> w \<noteq> \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> w)
                    \<longrightarrow> \<sigma>' i = \<sigma> i \<and> is_set_val(\<sigma>' w) \<and> (\<sigma>' w \<subset>\<^sub>r \<sigma> pw \<or> \<sigma> i \<notin>\<^sub>r \<sigma>' w)" 
        using not_member_rel_def remove_val_def subseteq_rel_def 
        by (metis Value.disc(9) Value.sel(3) finsertCI fminusE subset_rel_def)
      have both: "\<And>\<sigma> \<sigma>'. is_nat_val(\<sigma> i) \<and> \<sigma> w \<subseteq>\<^sub>r \<sigma> pw \<and> \<sigma> nw = \<sigma> pw -\<^sub>v \<sigma> i \<and> is_set_val(\<sigma> pw) \<and> \<sigma>' i = \<sigma> i \<and> (\<sigma> w = \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> nw) \<and> (\<sigma> w \<noteq> \<sigma> pw \<longrightarrow> \<sigma>' w = \<sigma> w)
                  \<longrightarrow> \<sigma>' w \<subseteq>\<^sub>r \<sigma> w \<and> \<sigma> w -\<^sub>s \<sigma>' w \<subseteq>\<^sub>r set_val{|vi \<sigma>|} \<and> \<sigma>' i = \<sigma> i \<and> is_set_val(\<sigma>' w) \<and> (\<sigma>' w \<subset>\<^sub>r \<sigma> pw \<or> \<sigma> i \<notin>\<^sub>r \<sigma>' w)"
        using show_g show_post by auto 
      have id_i: "id_bar{|w|} \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i}"
        unfolding id_bar_def get_var by force
      show ?thesis unfolding w_pre_def g_def CAS_post_def p_def nw_pre_def
        using both id_i restrict_domain_def subset_eq 
        by (smt (z3) IntE Int_subset_iff case_prodD case_prodE case_prodI mem_Collect_eq)
    qed
    show ?thesis using atomic_strengthen_spec strengthen 
      by (simp add: conj.sync_mono_right domain_restrict_inter)  
  qed 
  have e: "id_bar{|w|} \<subseteq> id i"
    unfolding id_bar_def id_def by blast  
  have f: "?rhs \<ge> \<langle>UNIV, id_bar{|w|} \<inter> CAS_post\<rangle>" (is "_ \<ge> ?rhs")
    using rely_remove atomic_spec_weaken_pre by (meson dual_order.trans subset_UNIV)
  have i: "?rhs \<ge> CAS" unfolding CAS_def CAS_post_def
    using assert_top atomic_spec_def distrib_seq_conj_guar_pgm guar_idle guar_opt id_bar_refl var_frame_expand by auto
  show ?thesis using a b c d f i
    by (meson dual_order.trans) 
qed

lemma helper:
  assumes "c1 \<ge> d1"
  assumes "c2 \<ge> d2"
  assumes "c3 \<ge> d3"
  shows "c1 ; c2 ; c3 \<ge> d1 ; d2 ; d3" 
  by (simp add: assms(1) assms(2) assms(3) seq_mono)

lemma refine_body:
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>b_t \<inter> p \<inter> fn_less vw (wfr\<^sup>=) k\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less vw wfr k \<union> b_x))\<rparr> \<ge> body"
proof -
  have wfr_simp: "\<And>k. fn_less vw (wfr\<^sup>=) k = {\<sigma>. vw \<sigma> |\<subseteq>| k}" 
    unfolding fn_less_def wfr_def by blast
  have wfreq_simp: "\<And>k. fn_less vw wfr k = {\<sigma>. vw \<sigma> |\<subset>| k}"
    unfolding fn_less_def  wfr_def by auto
  have a: "rely r \<iinter> guar g \<iinter> \<lbrace>b_t \<inter> p \<inter> fn_less vw (wfr\<^sup>=) k\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less vw wfr k \<union> b_x))\<rparr> \<ge>
           rely r \<iinter> guar g \<iinter> \<lbrace>b_t \<inter> p \<inter> {\<sigma>. vw \<sigma> |\<subseteq>| k}\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> ({\<sigma>. vw \<sigma> |\<subset>| k} \<union> b_x))\<rparr>"
            (is "_ \<ge> ?rhs")
    using wfr_simp wfreq_simp by fastforce
  also have b: "?rhs \<ge> rely r \<iinter> guar g \<iinter> \<lbrace>b_t \<inter> p \<inter> {\<sigma>. vw \<sigma> |\<subseteq>| k}\<rbrace>; \<lparr>goal w\<rparr>"
            (is "_ \<ge> ?rhs")
  proof -
    have ba: "q \<subseteq> q\<^sup>*" 
      by blast 
    have bb: "p \<inter> ({\<sigma>. vw \<sigma> |\<subset>| k} \<union> b_x) = {\<sigma>. is_set_val(\<sigma> w) \<and> is_nat_val(\<sigma> i) \<and> (vw \<sigma> |\<subset>| k \<or> \<sigma> i \<notin>\<^sub>r \<sigma> w)}"
      unfolding p_def b_x_def using b_f_def by fastforce
    have bc: "q\<^sup>* \<triangleright> (p \<inter> ({\<sigma>. vw \<sigma> |\<subset>| k} \<union> b_x)) \<supseteq> q \<inter> range_restriction (p \<inter> ({\<sigma>. vw \<sigma> |\<subset>| k} \<union> b_x))"
              (is "_ \<supseteq> ?rh")
      using restrict_range_def ba by auto   
    have bd: "?rh = {(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i} \<inter> {(\<sigma>,\<sigma>'). is_set_val(\<sigma>' w) \<and> is_nat_val(\<sigma>' i) \<and> (vw \<sigma>' |\<subset>| k \<or> \<sigma>' i \<notin>\<^sub>r \<sigma>' w)}"
      unfolding q_def using bb bc 
      by force
    have be: "(b_t \<inter> p \<inter> {\<sigma>. vw \<sigma> |\<subseteq>| k}) \<triangleleft> goal w \<subseteq> 
              {(\<sigma>,\<sigma>'). is_set_val(\<sigma> w) \<and> is_nat_val(\<sigma> i) \<and> vw \<sigma> |\<subseteq>| k \<and> \<sigma>' i = \<sigma> i \<and> (vw \<sigma>' |\<subset>| k \<or> \<sigma>' i \<notin>\<^sub>r \<sigma>' w)}"
    proof -
      have bea: "b_t \<inter> p \<inter> {\<sigma>. vw \<sigma> |\<subseteq>| k} = p \<inter> {\<sigma>. vw \<sigma> |\<subseteq>| k}"
        unfolding b_t_def by auto 
      have beb: "\<dots> = {\<sigma>. is_set_val(\<sigma> w) \<and> is_nat_val(\<sigma> i) \<and> vw \<sigma> |\<subseteq>| k}"
        unfolding p_def by fastforce
      show ?thesis unfolding goal_def using bea beb
        by (smt (z3) domain_restricts_contains pfsubset_fsubset_trans subset_rel_def vw_def)   
    qed
    have bf: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). vw \<sigma>' |\<subset>| k \<or> \<sigma>' i \<notin>\<^sub>r \<sigma>' w}"
      by fastforce
    have bg: "p \<triangleleft> goal w \<subseteq> {(\<sigma>,\<sigma>'). is_set_val(\<sigma>' w) \<and> is_nat_val(\<sigma>' i)}"
      unfolding p_def goal_def restrict_domain_def by force
    have bh:"(b_t \<inter> p \<inter> {\<sigma>. vw \<sigma> |\<subseteq>| k}) \<triangleleft> goal w \<subseteq> 
                   {(\<sigma>,\<sigma>'). is_set_val(\<sigma>' w) \<and> is_nat_val(\<sigma>' i) \<and> \<sigma>' i = \<sigma> i \<and> (vw \<sigma>' |\<subset>| k \<or> \<sigma>' i \<notin>\<^sub>r \<sigma>' w)}"
      using be bg 
      by (smt (z3) Ball_Collect case_prodD case_prodI domain_restrict_remove mem_Collect_eq goal_def subrelI) 
    have bi: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). \<sigma>' i = \<sigma> i} \<inter> {(\<sigma>,\<sigma>'). is_set_val(\<sigma>' w) \<and> is_nat_val(\<sigma>' i) \<and> (vw \<sigma>' |\<subset>| k \<or> \<sigma>' i \<notin>\<^sub>r \<sigma>' w)}"
      by (smt (z3) IntI bg case_prodE case_prod_conv mem_Collect_eq subset_iff) 
    have bj: "\<dots> \<subseteq> q\<^sup>* \<triangleright> (p \<inter> ({\<sigma>. vw \<sigma> |\<subset>| k} \<union> b_x))"
      using bc bd 
      by (smt (z3) Collect_mono_iff IntI bg case_prodE case_prod_conv mem_Collect_eq subsetI) 
    show ?thesis using spec_strengthen_under_pre bh bi bj
      using conj.sync_mono_right by (meson dual_order.trans)
  qed
  also have c: "?rhs \<ge> rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; {|nw,pw,w|}:\<^sub>s\<lparr>goal w\<rparr>" 
            (is "_ \<ge> ?rhs")
    by (metis assert_remove_left assert_seq_assert conj.sync_mono_right guar_intro_guar_pgm seq_mono
        seq_nil_right var_frame_set_def)
  also have d: "?rhs \<ge> rely r \<iinter> guar g \<iinter> (\<lbrace>p\<rbrace> ; pw:\<^sub>f\<lparr>pw_post\<rparr> ; \<lbrace>nw_pre\<rbrace>; nw:\<^sub>f\<lparr>nw_post\<rparr> ; \<lbrace>w_pre\<rbrace> ; w:\<^sub>f\<lparr>goal pw\<rparr>)"
            (is "_ \<ge> ?rhs")
    using Example16_17 conj.sync_mono_right by presburger 
  also have e: "?rhs \<ge> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; pw:\<^sub>f\<lparr>pw_post\<rparr>) ;
                  (rely r \<iinter> guar g \<iinter> \<lbrace>nw_pre\<rbrace> ; nw:\<^sub>f\<lparr>nw_post\<rparr>) ;
                  (rely r \<iinter> guar g \<iinter> \<lbrace>w_pre\<rbrace> ; w:\<^sub>f\<lparr>goal pw\<rparr>)"
            (is "_ \<ge> ?rhs")    
    using distrib_seq_conj_guar_pgm distrib_seq_conj_rely local.conj_assoc seq_assoc by force 
  also have f: "?rhs \<ge>  pw ::= expr_w ; nw ::= pw_minus_i ; CAS"
    using helper assign_pw assign_nw intro_CAS by blast 
  show ?thesis using a b c d e f 
    using body_def by force
qed


lemma remove_rely_loop_early:
  shows "guar g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> b_f)\<rparr> \<ge> while b do body od"
proof -
  have wellfounded: "wf wfr" (* |\<subset>| *)
    unfolding wfr_def subset_rel_def using wfP_pfsubset wfP_def by blast   
  have wfr_trans: "trans wfr" 
  proof -
    have trans: "\<forall>x y z. (x,y) \<in> wfr \<and> (y,z) \<in> wfr \<longrightarrow> (x,z) \<in> wfr"
      unfolding wfr_def subset_rel_def by blast 
    show ?thesis using trans using trans_def by blast
  qed
  have single_reference_b: "single_reference b r" 
  proof -
    have single_reference_i: "single_reference expr_i r"
      by (simp add: expr_i_def)
    have single_reference_w: "single_reference expr_w r"
      by (simp add: expr_w_def)
    have estable_i: "estable expr_i r"
      unfolding estable_def expr_i_def r_def by force
    show ?thesis using single_reference_i single_reference_w estable_i by (simp add: b_def)
  qed
  have tolerate_interference: "tolerates_interference p (q\<^sup>* \<triangleright> p) r"
    unfolding tolerates_interference_def stable_def restrict_range_def restrict_domain_def p_def q_def r_def  
    using stable_p apply auto 
       apply (simp add: ImageI Relations.stable_def in_mono) 
    apply (metis (mono_tags, lifting) case_prodI mem_Collect_eq r_into_rtrancl rtrancl_trans)
    by (meson CollectI case_prodI rtrancl.rtrancl_into_rtrancl)
  have b_boolean: "p \<subseteq> expr_type b boolean"
    unfolding expr_type_def b_def expr_eq_def 
    by (simp add: false_Value_def member_val_def subsetI true_Value_def) 
  have pb_establishes_b_t: "p \<inter> expr_eq b true \<subseteq> b_t" 
    by (simp add: b_t_def)
  have pr_maintains_b_t: "stable b_t (p \<triangleleft> r)" (*b_t is stable under interference satisfying p \<triangleleft> r*)  
    by (simp add: Relations.stable_def b_t_def)
  have pnegb_establishes_b_f: "p \<inter> expr_eq b false \<subseteq> b_f"
    unfolding expr_eq_def b_def expr_i_def expr_w_def b_f_def 
    by (simp add: false_Value_def member_val_def not_member_rel_def) 
  have pr_maintains_b_f: "stable b_f (p \<triangleleft> r)" (*b_f is stable under interference satisfying p \<triangleleft> r*)
  proof -
    have a: "\<And>\<sigma> \<sigma>'. \<sigma> i \<notin>\<^sub>r \<sigma> w \<and> \<sigma>' w \<subseteq>\<^sub>r \<sigma> w \<and> \<sigma> i = \<sigma>' i \<longrightarrow> \<sigma>' i \<notin>\<^sub>r \<sigma>' w" 
      by (metis not_member_rel_def pfsubsetD subset_rel_def subseteq_rel_def) 
    have b: "stable b_f r" unfolding stable_def b_f_def r_def
      using a by (smt (verit) Ball_Collect ImageE case_prodD mem_Collect_eq) 
    show ?thesis by (meson b domain_restrict_remove stable_antimono_r)
  qed
  have pb_x_establishes_b_false: "p \<inter> b_x \<subseteq> expr_eq b false" 
    unfolding b_x_def b_f_def p_def b_def expr_eq_def using eval_def apply auto 
    by (simp add: expr_i_def expr_w_def false_Value_def member_val_def not_member_rel_def) 
  have pr_maintains_b_x: "stable b_x (p \<triangleleft> r)" (*b_x is stable under interference satisfying p \<triangleleft> r*) 
    using b_x_def pr_maintains_b_f by force
  have pr_variant: "p \<triangleleft> r \<subseteq> dec (wfr\<^sup>=) vw"
    unfolding p_def r_def wfr_def dec_variant_def using domain_restrict_remove 
    by (smt (verit, ccfv_threshold) UnCI case_prodI converse_iff domain_restricts_contains
        inv_image_def mem_Collect_eq pair_in_Id_conv subset_rel_def subseteq_rel_def vw_def) 
  have step: "\<forall>k::nat fset. guar g \<iinter> rely r \<iinter> \<lbrace>b_t \<inter> p \<inter> fn_less vw (wfr\<^sup>=) k\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less vw wfr k \<union> b_x))\<rparr> \<ge> body"
    using refine_body local.conj_commute by fastforce 
  show ?thesis using rely_loop_early refl_g wellfounded wfr_trans single_reference_b 
          tolerate_interference b_boolean pb_establishes_b_t pr_maintains_b_t
          pnegb_establishes_b_f pr_maintains_b_f pb_x_establishes_b_false pr_maintains_b_x
          pr_variant step by blast
qed

end
end