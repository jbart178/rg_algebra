theory State_Relations
  imports
  "Idle"
  "HOL-Library.FSet"
begin

text \<open>The axioms for setters and getters are axioms (a-e) from Section 5.2 of
      the Refinement Calculus book by Ralph-Johan Back and Joakim von Wright. \<close>

locale state_relations = idle_command (* lib_last
  for lib_last :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("L\<^sup>C\<^sub>_ _" [999, 999] 999) + *) +
  constrains test :: "'state set \<Rightarrow> 'a"
  constrains pgm ::  "'state rel \<Rightarrow> 'a"
  constrains env ::  "'state rel \<Rightarrow> 'a"
  fixes set_var   :: "'varname \<Rightarrow> 'v \<Rightarrow> 'state \<Rightarrow> 'state"
  fixes get_var   :: "'varname \<Rightarrow> 'state \<Rightarrow> 'v" 
  assumes set_get: "\<And>k s. (set_var k (get_var k s) s) = s"
  assumes get_set1: "\<And>k x s. get_var k (set_var k x s) = x"
  assumes get_set2: "\<And>k x k' s. k \<noteq> k' \<Longrightarrow> get_var k' (set_var k x s) = get_var k' s"
  assumes set_set1: "\<And>k x x' s. set_var k x (set_var k x' s) = set_var k x s"
  assumes set_set2: "\<And>k x x' s. k \<noteq> k' \<Longrightarrow> set_var k x (set_var k' x' s) = set_var k' x' (set_var k x s)"
begin

text \<open>The identity relation on all variables not in the set $vars$. \<close>
definition id_bar :: "'varname fset \<Rightarrow> 'state rel"
  where "id_bar vars = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<notin>| vars \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"

lemma id_bar_narrow:
  assumes "X |\<subseteq>| Y"
  shows "id_bar X \<subseteq> id_bar Y"
proof -
  have a: "id_bar X = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<notin>| X \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"
    using id_bar_def by presburger
  have b: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<notin>| Y \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}" 
    using assms by auto
  show ?thesis using a b id_bar_def by presburger
qed

text \<open>Add a frame of $vars$ to a command $c$.\<close>
definition var_frame_set :: "'varname fset \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>s" 95)
  where "var_frame_set vars c \<equiv> (guar (id_bar vars)) \<iinter> c"

text \<open>Add a frame of a single variable $x$ to a command $c$.\<close>
definition var_frame :: "'varname \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>f" 95)
  where "var_frame x c \<equiv> {|x|}:\<^sub>sc"

lemma var_frame_expand: "x:\<^sub>fc = (guar (id_bar {|x|})) \<iinter> c"
  using var_frame_def var_frame_set_def by simp

text \<open>Set of states in which variable $var$ equals $value$.\<close>
definition var_eq :: "'varname => 'v \<Rightarrow> 'state set"
  where "var_eq var value \<equiv> {s. get_var var s = value}"

definition id_set :: "'varname fset \<Rightarrow> 'state rel"
  where "id_set vars = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<in>| vars \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"

lemma id_set_narrow:
  assumes "X |\<subseteq>| Y"
  shows "id_set Y \<subseteq> id_set X"
proof -
  have a: "id_set Y = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<in>| Y \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"
    using id_set_def by presburger
  have b: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<in>| X \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}" 
    using assms by auto
  show ?thesis using a b id_set_def by presburger
qed

definition id :: "'varname \<Rightarrow> 'state rel"
  where "id x = {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'}"

lemma id_consistent : "id(x) = id_set {|x|}"
  using id_set_def local.id_def by auto 

lemma id_univ : "id(x) O id_bar({|x|}) = UNIV"
proof -
  have "id(x) O id_bar({|x|}) = {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} O 
      {(\<sigma>,\<sigma>'). \<forall>x'::'varname. x' |\<notin>| {|x|} \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>'}"
    unfolding id_def id_bar_def by simp
  also have "... = {(\<sigma>, \<sigma>'). (\<exists>\<sigma>''. (\<sigma>, \<sigma>'') \<in> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} \<and>
      (\<sigma>'', \<sigma>') \<in> {(\<sigma>,\<sigma>'). \<forall>x'::'varname. x' \<noteq> x \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>'})}"
    by (simp add: relcomp_unfold)
  also have "... = {(\<sigma>, \<sigma>'). True}"
  proof -
    have "\<exists>\<sigma>''. (\<sigma>,\<sigma>'') \<in> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} \<and> (\<sigma>'',\<sigma>') \<in> {(\<sigma>,\<sigma>'). \<forall>x'. (x' \<noteq> x \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>')}" for \<sigma> \<sigma>'
      by (intro exI[of _ "set_var x (get_var x \<sigma>) \<sigma>'"]) (simp add: get_set1 get_set2)
    then show ?thesis by auto
  qed
  finally show ?thesis by simp
qed

text \<open>Expand a frame as a guarantee and merge with the existing guarantee.\<close>

lemma expand_frame_spec:
  shows "guar g \<iinter> \<lbrace>p\<rbrace>;x:\<^sub>fc = guar(id_bar{|x|} \<inter> g) \<iinter> \<lbrace>p\<rbrace>;c"
proof -
  have a: "guar g \<iinter> \<lbrace>p\<rbrace>;x:\<^sub>fc = \<lbrace>p\<rbrace>;(guar g \<iinter> guar(id_bar{|x|}) \<iinter> c)"
    by (simp add: conj.assert_distrib local.conj_assoc var_frame_expand) 
  have merge: "guar g \<iinter> guar(id_bar{|x|}) = guar(id_bar{|x|} \<inter> g)"
    using guar_merge by (simp add: Int_commute)
  show ?thesis using a merge conj.assert_distrib by presburger
qed

lemma id_set_trans: "(id_set Y)\<^sup>* = id_set Y"
proof -
  have a: "id_set Y \<subseteq> (id_set Y)\<^sup>*"
    by blast
  have b: "(id_set Y) O (id_set Y) \<subseteq> (id_set Y)"
    using id_set_def by force 
  have c: "Id \<subseteq> id_set Y"
    using id_set_def by force 
  have c: "(id_set Y)\<^sup>* \<subseteq> id_set Y"
    by (simp add: Int_absorb2 Int_commute a b c rtrancl_Int_subset) 
  show ?thesis 
    using c by blast 
qed

lemma frame_restrict:
  assumes restrict_set: "Z |\<subseteq>| X"
  assumes nochange_Y: "Y |\<inter>| X = {||}"
  assumes rely_nochange_Y: "r \<subseteq> id_set Y"
  shows "rely r \<iinter> X:\<^sub>s\<lparr>q \<inter> (id_set Y)\<rparr> \<ge> rely r \<iinter> Z:\<^sub>s\<lparr>q\<rparr>"
proof -            
  have r_nochange_Y: "r = r \<inter> (id_set Y)" 
    using rely_nochange_Y by blast 
  have g_nochange_Y: "id_bar X \<subseteq> id_set Y"
    using nochange_Y id_set_narrow id_bar_def id_set_def by auto
  have g_nochange_Ya: "id_set Y \<inter> id_bar X = id_bar X"
    using g_nochange_Y by blast 
  have bar_X_Z: "id_bar Z \<subseteq> id_bar X"
    using restrict_set id_bar_narrow by presburger
  have a: "rely r \<iinter> X:\<^sub>s\<lparr>q \<inter> (id_set Y)\<rparr> = rely r \<iinter> guar(id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>" 
    using local.conj_assoc var_frame_set_def by presburger
  have b: "\<dots> = rely(r \<inter> (id_set Y)) \<iinter> guar(id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>"
    using r_nochange_Y by presburger
  have c: "\<dots> = rely r \<iinter> rely(id_set Y) \<iinter> guar(id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>" 
    using rely_conj_rely by presburger 
  have d: "\<dots> = rely r \<iinter> rely(id_set Y) \<iinter> guar(id_set Y \<inter> id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>" 
    using g_nochange_Ya by presburger 
  have e: "\<dots> = rely r \<iinter> rely(id_set Y) \<iinter> guar(id_set Y) \<iinter> guar(id_bar X) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>" 
    using guar_merge local.conj_assoc by presburger
  have f: "\<dots> = rely r \<iinter> guar(id_bar X) \<iinter> (rely(id_set Y) \<iinter> guar(id_set Y) \<iinter> \<lparr>q \<inter> (id_set Y)\<rparr>)" 
    using guar_merge local.conj_assoc local.conj_commute by fastforce
  have g: "\<dots> = rely r \<iinter> guar(id_bar X) \<iinter> (rely(id_set Y) \<iinter> guar(id_set Y) \<iinter> \<lparr>q \<inter> (id_set Y)\<^sup>*\<rparr>)"
    using id_set_trans by presburger 
  have h: "\<dots> = rely r \<iinter> guar(id_bar X) \<iinter> (rely(id_set Y) \<iinter> guar(id_set Y) \<iinter> \<lparr>q\<rparr>)"
    using spec_trading by (metis Int_commute Un_absorb) 
  have i: "\<dots> = rely r \<iinter> rely(id_set Y) \<iinter> guar(id_set Y) \<iinter> guar(id_bar X) \<iinter> \<lparr>q\<rparr>"
    using conj.comm.left_commute local.conj_commute by presburger
  have j: "\<dots> = rely(r \<inter> id_set Y) \<iinter> guar(id_set Y \<inter> id_bar X) \<iinter> \<lparr>q\<rparr>"
    using guar_merge local.conj_assoc rely_conj_rely by presburger
  have k: "\<dots> = rely r \<iinter> guar(id_bar X) \<iinter> \<lparr>q\<rparr>"
    using r_nochange_Y g_nochange_Ya by presburger
  have l: "\<dots> \<ge> rely r \<iinter> guar(id_bar Z) \<iinter> \<lparr>q\<rparr>"
    using guar_strengthen bar_X_Z conj.sync_mono_left conj.sync_mono_right by presburger
  show ?thesis using a b c d e f g h i j k l var_frame_set_def local.conj_assoc by force 
qed

end

end
