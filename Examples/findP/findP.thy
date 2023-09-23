section \<open>Find Least First Element That Satisfies $P$\<close>

theory findP
  imports  
  "programming_constructs_extended"
begin

subsection \<open>Proof Constructs\<close>
subsubsection \<open>State Description\<close>
text \<open>This record describes the components of the state of the program. 
$oc$ and $ec$ are included as part of the state and not as local variables for this proof.\<close>
record state =
  t :: nat
  et :: nat
  ot :: nat
  ec :: nat
  oc :: nat
(*describe a get and set function to access the components of the record*)
datatype varname = Vt | Vet | Vot | Vec | Voc

fun get_var :: "varname \<Rightarrow> state \<Rightarrow> nat" where
  "get_var Vt s = t s" |
  "get_var Vet s = et s" |
  "get_var Vot s = ot s" |
  "get_var Vec s = ec s" |
  "get_var Voc s = oc s" 

fun set_var :: "varname \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "set_var Vt val s = s\<lparr>t := val\<rparr>" |
  "set_var Vet val s = s\<lparr>et := val\<rparr>" |
  "set_var Vot val s = s\<lparr>ot := val\<rparr>" |
  "set_var Vec val s = s\<lparr>ec := val\<rparr>" |
  "set_var Voc val s = s\<lparr>oc := val\<rparr>" 

subsubsection \<open>Value Definition\<close>
text \<open>An additional datatype, denoted a "Value" is used throughout the proof.\<close>
datatype Value = Natural (the_Nat:"nat") | Bool (the_Bool:"bool")

instantiation Value :: has_booleans
begin
  definition true_Value :: "Value" where
    "true_Value = Bool True"
  definition false_Value :: "Value" where
    "false_Value = Bool False"

  instance proof
    show "(has_booleans_class.true::Value) \<noteq> has_booleans_class.false"
      by (simp add: true_Value_def false_Value_def)
  qed
end

definition Nat_less_than :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "<\<^sub>n" 50)
  where "Nat_less_than m n = Bool (the_Nat m < the_Nat n)"

definition Bool_and :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "\<and>\<^sub>n" 50)
  where "Bool_and m n = Bool (the_Bool m \<and> the_Bool n)"

subsubsection \<open>Definitions\<close>
text \<open>This section covers the fundamental definitions used for the proof.\<close>
locale findP_rules =
  fixes v :: "nat \<Rightarrow> 'd" and
        Pr :: "'d \<Rightarrow> bool" and
        N :: "nat" 
begin

definition 
P :: "nat \<Rightarrow> bool" where
"P i \<equiv> (i < N) \<longrightarrow> (Pr (v i))"

definition
minP :: "nat set \<Rightarrow> nat" where
"minP S = Min {i | i. i \<in> S \<and> (P i)}"

definition
inv :: "nat \<Rightarrow> nat set \<Rightarrow> bool " where
"inv st S \<equiv> ((st \<noteq> N) \<longrightarrow> (st = (minP S)))"

definition
inv_loop :: "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool" where
"inv_loop sc st S \<equiv> sc \<le> minP S \<and> sc \<in> S \<and> sc \<le> st + 1"

text \<open>Evens, odds and nats are bounded by N + 1 as Min operations require finite sets.\<close>
definition
even :: "nat set" where
"even = {k. k mod 2 = 0 \<and> k \<le> N + 1}"

definition
odd :: "nat set" where
"odd = {k. k mod 2 = 1 \<and> k \<le> N + 1}"

definition
nats :: "nat set" where
"nats = {k. k \<le> N + 1}"
end

subsubsection \<open>Proof Instantiation\<close> 
text \<open>This locale instantiates the proof on top of the existing theory using the described 
\textit{set\_var} and \textit{get\_var} functions.\<close>
locale findP_pre = while_loop + intro_par_big + assignments +
  constrains test :: "state set \<Rightarrow> 'a" 
  constrains pgm :: "state rel \<Rightarrow> 'a"
  constrains env :: "state rel \<Rightarrow> 'a"
  constrains get_var :: "varname \<Rightarrow> state \<Rightarrow> nat"
  constrains var_eq :: "varname \<Rightarrow> nat \<Rightarrow> (state set)"
  constrains assign :: "varname \<Rightarrow> (state, nat) expr \<Rightarrow> 'a"
  constrains var_frame_set :: "varname set \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains var_frame :: "varname \<Rightarrow> 'a \<Rightarrow> 'a"
begin

lemma set_get_consistent : "set_var k (get_var k s) s = s"
  by (simp add: set_get)

sublocale programming_constructs_extended seq test par conj pgm env set_var get_var
           (* lib lib_first lib_last lib_bool_sets bool_first_sets bool_last_sets 
            lib_bool bool_first bool_last *)
  sorry
(*proof 
  show "\<And>k s. set_var k (get_var k s) s = s" using set_get_consistent by simp
qed *)

(*
notation 
  assign (infix "::=" 60) and
  var_frame (infix ":\<^sub>f" 60)
*)
end                  

subsection \<open>Abbreviations\<close>
text \<open>This section contains abbreviations used throughout the proof.\<close>
locale findP_abbreviations = findP_pre + findP_rules
begin

subsubsection \<open>General Abbreviations\<close>
abbreviation p_inv :: "state set" where
"p_inv \<equiv> {s. inv (ot s) odd \<and> inv (et s) even}"

abbreviation p_inv_ext :: "state set" where
"p_inv_ext \<equiv> {s. inv (ot s) odd \<and> inv (et s) even \<and> inv_loop (ec s) (et s) even}"

abbreviation no_change :: "state rel" where
"no_change \<equiv> {(s, s'). s' = s}"

abbreviation ot_decreq :: "state rel" where
"ot_decreq \<equiv> {(s, s'). ot s' \<le> ot s \<and> et s = et s' \<and> ec s = ec s'}"

abbreviation et_decreq :: "state rel" where
"et_decreq \<equiv> {(s, s'). et s' \<le> et s \<and> ot s = ot s' \<and> oc s = oc s'}"

subsubsection \<open>Assignment Abbreviations\<close>
abbreviation var_init :: 'a where
"var_init \<equiv> rely{(s, s'). s' = s} \<iinter> \<lparr>{(s, s'). ot s' = N \<and> et s' = N}\<rparr>"

abbreviation ec_to_0 :: "state rel" where
"ec_to_0 \<equiv> {(s, s'). ec s' = 0 \<and> et s = et s' \<and> (inv (ot s) odd \<longrightarrow> inv (ot s') odd)}"

abbreviation var_init_ec :: 'a where
"var_init_ec \<equiv> guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>"

abbreviation post_assign_t :: "'a" where
"post_assign_t \<equiv> guar {(s, s'). et s' = et s \<and> ot s' = ot s} \<iinter> rely {(s, s'). s' = s} \<iinter> 
      \<lparr>{(s, s'). t s' = min (et s') (ot s') \<and> ot s = ot s' \<and> et s = et s' }\<rparr>"

subsubsection \<open>While Loop Abbreviations (w)\<close>
abbreviation ec_lt_ot :: "(state, Value) expr" where
"ec_lt_ot \<equiv> (BinaryOp (<\<^sub>n) (Variable (\<lambda>s::state. Natural(ec s))) 
      (Variable (\<lambda>s::state. Natural(ot s))))"

abbreviation ec_lt_et :: "(state, Value) expr" where
"ec_lt_et \<equiv> (BinaryOp (<\<^sub>n) (Variable (\<lambda>s::state. Natural(ec s))) 
      (Variable (\<lambda>s::state. Natural(et s))))"

abbreviation b\<^sub>w :: "(state, Value) expr" where
"b\<^sub>w \<equiv> BinaryOp (\<and>\<^sub>n) ec_lt_et ec_lt_ot"

abbreviation b0\<^sub>w :: "state set" where
"b0\<^sub>w \<equiv> {s::state. ec s < et s}"

abbreviation b1\<^sub>w :: "state set" where
"b1\<^sub>w \<equiv> {s. ec s \<ge> et s \<or> ec s \<ge> ot s}"

abbreviation v\<^sub>w :: "state \<Rightarrow> nat" where
"v\<^sub>w \<equiv> (\<lambda>s::state. et s - ec s)"

abbreviation p\<^sub>w :: "state set" where
"p\<^sub>w \<equiv> p_inv_ext"

abbreviation q\<^sub>w :: "state rel" where
"q\<^sub>w \<equiv> UNIV"

abbreviation r\<^sub>w :: "state rel" where
"r\<^sub>w \<equiv> (ot_decreq \<inter> P' p_inv)"

abbreviation g\<^sub>w :: "state rel" where
"g\<^sub>w \<equiv> (et_decreq \<inter> P' p_inv)"

abbreviation wfr\<^sub>w :: "nat rel" where 
"wfr\<^sub>w \<equiv> {((n::nat), n'). n < n' \<and> n' \<le> N + 1}"

abbreviation c\<^sub>w_pre :: "state set" where
"c\<^sub>w_pre \<equiv> {s. ec s < et s \<and> inv_loop (ec s) (et s) even \<and> inv (et s) even}"

abbreviation c\<^sub>w_post :: "state rel" where
"c\<^sub>w_post \<equiv> {(s, s'). inv_loop (ec s') (et s') even \<and> 
      0 \<le> 1 + et s' - ec s' \<and> et s' - ec s' < et s - ec s}"
(*      (-1 \<le> (et s') - (ec s')) \<and> (et s') - (ec s') < (et s) - (ec s)}" *)

abbreviation c\<^sub>w :: 'a where
"c\<^sub>w \<equiv> rely r\<^sub>w \<iinter> guar g\<^sub>w \<iinter> \<lbrace>c\<^sub>w_pre\<rbrace>;\<lparr>c\<^sub>w_post\<rparr>"

subsubsection \<open>If Statement Abbreviations (i)\<close>
abbreviation b\<^sub>i :: "(state, Value) expr" where
"b\<^sub>i \<equiv> Variable (\<lambda>s::state. Bool(P(ec s)))"

abbreviation b0\<^sub>i :: "state set" where
"b0\<^sub>i \<equiv> {s. P(ec s)}"

abbreviation b1\<^sub>i :: "state set" where
"b1\<^sub>i \<equiv> {s. \<not>(P(ec s))}"

abbreviation r\<^sub>i :: "state rel" where
"r\<^sub>i \<equiv> {(s, s'). ec s' = ec s \<and> et s' = et s}"

abbreviation g\<^sub>i :: "state rel" where
"g\<^sub>i \<equiv> et_decreq \<inter> P' p_inv"

abbreviation p\<^sub>i :: "state set" where
"p\<^sub>i \<equiv> {s. ec s < et s \<and> inv_loop (ec s) (et s) even \<and> inv (et s) even}"

abbreviation q\<^sub>i :: "state rel" where
"q\<^sub>i \<equiv> {(s, s'). inv_loop (ec s') (et s') even \<and> 
      0 \<le> 1 + et s' - ec s' \<and> et s' - ec s' < et s - ec s}"
(*      (-1 \<le> (et s') - (ec s')) \<and> (et s') - (ec s') < (et s) - (ec s)}" *)

abbreviation if1 :: 'a where
"if1 \<equiv> guar g\<^sub>i \<iinter> rely r\<^sub>i \<iinter> \<lbrace>b0\<^sub>i \<inter> p\<^sub>i\<rbrace> ; \<lparr>q\<^sub>i\<rparr>"

abbreviation if2 :: 'a where
"if2 \<equiv> guar g\<^sub>i \<iinter> rely r\<^sub>i \<iinter> \<lbrace>b1\<^sub>i \<inter> p\<^sub>i\<rbrace> ; \<lparr>q\<^sub>i\<rparr>"

subsubsection \<open>$ec$ Assignment Abbreviations (c) \<close>
abbreviation g\<^sub>c :: "state rel" where
"g\<^sub>c \<equiv> et_decreq \<inter> P' p_inv"

abbreviation r\<^sub>c :: "state rel" where
"r\<^sub>c \<equiv> ot_decreq \<inter> P' p_inv"

abbreviation p\<^sub>c :: "state set" where
"p\<^sub>c \<equiv> p_inv"

abbreviation q\<^sub>c :: "state rel" where
"q\<^sub>c \<equiv> ec_to_0"

abbreviation e\<^sub>c :: "(state, nat) expr" where
"e\<^sub>c \<equiv> Constant 0"

abbreviation e0\<^sub>c :: "nat \<Rightarrow> state set" where
"e0\<^sub>c \<equiv> (\<lambda>k. {s. k = 0})"

subsubsection \<open>$et$ Assignment Abbreviations (e) \<close>
abbreviation p\<^sub>e :: "state set" where
"p\<^sub>e \<equiv> UNIV"

abbreviation q\<^sub>e :: "state rel" where
"q\<^sub>e \<equiv> {(s, s'). et s' = N}"

abbreviation r\<^sub>e :: "state rel" where
"r\<^sub>e \<equiv> {(s, s'). s' = s}"

abbreviation g\<^sub>e :: "state rel" where
"g\<^sub>e \<equiv> UNIV"

abbreviation e\<^sub>e :: "(state, nat) expr" where
"e\<^sub>e \<equiv> Constant N"

abbreviation e0\<^sub>e :: "nat \<Rightarrow> state set" where
"e0\<^sub>e \<equiv> (\<lambda>k. {s. k = N})"

subsubsection \<open>$ot$ Assignment Abbreviations (o) \<close>
abbreviation p\<^sub>o :: "state set" where
"p\<^sub>o \<equiv> UNIV"

abbreviation q\<^sub>o :: "state rel" where
"q\<^sub>o \<equiv> {(s, s'). et s' = et s \<and> ot s' = N}"

abbreviation r\<^sub>o :: "state rel" where
"r\<^sub>o \<equiv> {(s, s'). s' = s}"

abbreviation g\<^sub>o :: "state rel" where
"g\<^sub>o \<equiv> UNIV"

abbreviation e\<^sub>o :: "(state, nat) expr" where
"e\<^sub>o \<equiv> Constant N"

abbreviation e0\<^sub>o :: "nat \<Rightarrow> state set" where
"e0\<^sub>o \<equiv> (\<lambda>k. {s. k = N})"

subsubsection \<open>Post Assignment Abbreviations (t) \<close>
abbreviation p\<^sub>t :: "state set" where
"p\<^sub>t \<equiv> UNIV"

abbreviation q\<^sub>t :: "state rel" where
"q\<^sub>t \<equiv> {(s, s'). t s' = min (et s') (ot s') \<and> ot s = ot s' \<and> et s = et s'}"

abbreviation g\<^sub>t :: "state rel" where
"g\<^sub>t \<equiv> {(s, s'). et s' = et s \<and> ot s' = ot s}"

abbreviation r\<^sub>t :: "state rel" where
"r\<^sub>t \<equiv> {(s, s'). s' = s}"

abbreviation e\<^sub>t :: "(state, nat) expr" where
"e\<^sub>t \<equiv> BinaryOp min (Variable et) (Variable ot)"

abbreviation e0\<^sub>t :: "nat \<Rightarrow> state set" where
"e0\<^sub>t \<equiv> (\<lambda>k. {s. min (et s) (ot s) = k})"

subsubsection \<open>True If Statement Abbreviations (1) \<close>
abbreviation p\<^sub>1 :: "state set" where
"p\<^sub>1 \<equiv> b0\<^sub>i \<inter> p\<^sub>i"

abbreviation q\<^sub>1 :: "state rel" where
"q\<^sub>1 \<equiv> q\<^sub>i"

abbreviation g\<^sub>1 :: "state rel" where
"g\<^sub>1 \<equiv> g\<^sub>i"

abbreviation r\<^sub>1 :: "state rel" where
"r\<^sub>1 \<equiv> r\<^sub>i"

abbreviation e\<^sub>1 :: "(state, nat) expr" where
"e\<^sub>1 \<equiv> Variable ec"

abbreviation e0\<^sub>1 :: "nat \<Rightarrow> state set" where
"e0\<^sub>1 \<equiv> (\<lambda>k. {s. ec s = k})"

subsubsection \<open>False If Statement Abbreviations (2) \<close>
abbreviation p\<^sub>2 :: "state set" where
"p\<^sub>2 \<equiv> b1\<^sub>i \<inter> p\<^sub>i"

abbreviation q\<^sub>2 :: "state rel" where
"q\<^sub>2 \<equiv> q\<^sub>i"

abbreviation g\<^sub>2 :: "state rel" where
"g\<^sub>2 \<equiv> g\<^sub>i"

abbreviation r\<^sub>2 :: "state rel" where
"r\<^sub>2 \<equiv> r\<^sub>i"

abbreviation e\<^sub>2 :: "(state, nat) expr" where
"e\<^sub>2 \<equiv> Variable (\<lambda>s. (ec s) + 2)"

abbreviation e0\<^sub>2 :: "nat \<Rightarrow> state set" where
"e0\<^sub>2 \<equiv> (\<lambda>k. {s. (ec s) + 2 = k})"

subsubsection \<open>Step Abbreviations\<close>
abbreviation s23_post :: "state rel" where
"s23_post \<equiv> {(s, s'). (ot s' \<le> minP even \<or> et s' = minP even) \<and> 
      (et s' \<le> minP odd \<or> ot s' = minP odd) \<and> t s' = min (et s') (ot s')}"

abbreviation s24_first_post :: "state rel" where
"s24_first_post \<equiv> {(s, s'). (ot s' \<le> minP even \<or> et s' = minP even) \<and> 
      (et s' \<le> minP odd \<or> ot s' = minP odd)}"

abbreviation s24_second_post :: "state rel" where
"s24_second_post \<equiv> {(s, s'). t s' = min (et s') (ot s') \<and> 
      ot s = ot s' \<and> et s = et s' }"

abbreviation q1_25 :: "state rel" where
"q1_25 \<equiv> {(s, s'). ot s' \<le> minP even \<or> et s' = minP even}"

abbreviation q2_25 :: "state rel" where
"q2_25 \<equiv> {(s, s'). et s' \<le> minP odd \<or> ot s' = minP odd}"

abbreviation e28_post :: "state rel" where
"e28_post \<equiv> {(s, s'). (ot s' \<le> minP even \<or> et s' = minP even) \<and> 
      inv_loop (ec s') (et s') even}"

abbreviation e29_post :: "state rel" where
"e29_post \<equiv> {(s, s'). inv_loop (ec s') (et s') even \<and> (ec s' \<ge> ot s' \<or> ec s' \<ge> et s')}"

abbreviation e31_loop :: 'a where
"e31_loop \<equiv> rely r\<^sub>i \<iinter> guar g\<^sub>i \<iinter> \<lbrace>p\<^sub>i\<rbrace>;\<lparr>q\<^sub>i\<rparr>"

subsubsection \<open>Odd Refinement Abbreviations\<close>
abbreviation oc_lt_et :: "(state, Value) expr" where
"oc_lt_et \<equiv> (BinaryOp (<\<^sub>n) (Variable (\<lambda>s::state. Natural (oc s))) 
      (Variable (\<lambda>s::state. Natural (et s))))"

abbreviation oc_lt_ot :: "(state, Value) expr" where
"oc_lt_ot \<equiv> (BinaryOp (<\<^sub>n) (Variable (\<lambda>s::state. Natural (oc s))) 
      (Variable (\<lambda>s::state. Natural (ot s))))"

abbreviation b\<^sub>w\<^sub>o :: "(state, Value) expr" where
"b\<^sub>w\<^sub>o \<equiv> BinaryOp (\<and>\<^sub>n) oc_lt_ot oc_lt_et"

abbreviation b\<^sub>i\<^sub>o :: "(state, Value) expr" where
"b\<^sub>i\<^sub>o \<equiv> Variable (\<lambda>s::state. Bool (P (oc s)))"

abbreviation e\<^sub>1\<^sub>o :: "(state, nat) expr" where
"e\<^sub>1\<^sub>o \<equiv> Variable oc"

abbreviation e\<^sub>2\<^sub>o :: "(state, nat) expr" where
"e\<^sub>2\<^sub>o \<equiv> Variable (\<lambda>s. (oc s) + 2)"
end

subsection \<open>Formal Proof\<close>
text \<open>This section contains the formal proof of \emph{Find least first element of an array that satisfies $P$}
as described in \emph{A Guid to Rely/Guarantee Thinking}.\<close>
locale findP = findP_abbreviations
begin

subsubsection \<open>Basic Proofs\<close>
text \<open>This section contains proofs relating to evens, odds, nats and the Min function.\<close>
lemma even_union_odd : "even \<union> odd = nats"
  unfolding odd_def nats_def even_def by auto

lemma joining_min : 
  assumes "finite S" and "finite T" and "S \<noteq> {}" and "T \<noteq> {}"
  shows "min (Min S) (Min T) = Min (S \<union> T)"
  by (simp add: Min.union assms(1) assms(2) assms(3) assms(4))

lemma even_non_empty :  
  shows "{i |i. i \<in> even \<and> P i} \<noteq> {}"
proof (cases "N mod 2 = 0") 
  case True
  then have "N \<in> {i |i. i \<in> even \<and> P i}" unfolding even_def P_def by auto
  thus ?thesis by auto
next
  case False
  then have "(N + 1) \<in> {i |i. i \<in> even \<and> P i}" 
    unfolding even_def P_def by (auto, presburger)
  thus ?thesis by auto
qed

lemma odd_non_empty :
  shows "{i |i. i \<in> odd \<and> P i} \<noteq> {}"
proof (cases "N mod 2 = 1") 
  case True
  then have "N \<in> {i |i. i \<in> odd \<and> P i}" unfolding odd_def P_def by auto
  thus ?thesis by auto
next
  case False
  then have "(N + 1) \<in> {i |i. i \<in> odd \<and> P i}" unfolding odd_def P_def by auto
  thus ?thesis by auto
qed

lemma finite_even : " finite {i | i. i \<in> even \<and> (P i)}"
  unfolding even_def by auto

lemma finite_odd : "finite {i | i. i \<in> odd \<and> (P i)}"
  unfolding odd_def by auto

lemma containment :
  assumes "l = Min S" and "finite S" and "S \<noteq> {}"
  shows "l \<in> S"
  using assms by simp

subsubsection \<open>minP Proofs\<close>
text \<open>This section contains proofs relating to the minP function.\<close>
lemma joining_minP :
  shows "min (minP even) (minP odd) = minP (even \<union> odd)"
proof -
  have "{i |i. i \<in> even \<and> P i} \<union> {i |i. i \<in> odd \<and> P i} = {i |i. i \<in> even \<union> odd \<and> P i}" by auto
  moreover have "min (minP even) (minP odd) = 
        Min ({i |i. i \<in> even \<and> P i} \<union> {i |i. i \<in> odd \<and> P i})" 
    unfolding minP_def using finite_even finite_odd odd_non_empty 
      even_non_empty joining_min by fastforce
  ultimately show ?thesis unfolding minP_def by simp
qed

lemma minP_even_upper_bound : 
  shows "minP even \<le> N + 1"
proof -
  have "\<forall> e \<in> {i |i. i \<in> even \<and> P i}. e \<le> N + 1" 
    unfolding even_def by auto
  then show "minP even \<le> N + 1" 
    unfolding minP_def using finite_even even_non_empty Min_in by auto
qed

lemma minP_odd_upper_bound :
  shows "minP odd \<le> N + 1"
proof -
  have "\<forall> e \<in> {i |i. i \<in> odd \<and> P i}. e \<le> N + 1"
    unfolding odd_def by auto
  then show "minP odd \<le> N + 1" 
    unfolding minP_def using finite_odd odd_non_empty Min_in by auto
qed

lemma minP_even_upper_bound_restrict :
  assumes "minP even \<le> minP odd"
  shows "minP even \<le> N"
proof (rule ccontr)
  assume "\<not>(minP even \<le> N)"
  then have minP_value : "minP even = N + 1" 
    using minP_even_upper_bound by simp
  then have "N + 1 \<in> {i |i. i \<in> even \<and> P i}"
    unfolding minP_def using finite_even even_non_empty containment by fastforce
  then have "(N + 1) mod 2 = 0" unfolding even_def by auto
  moreover have "(N + 1) mod 2 = 1"
  proof -
    have "minP odd = N + 1" 
      using minP_odd_upper_bound assms minP_value by simp
    then have "N + 1 \<in> {i |i. i \<in> odd \<and> P i}" 
      unfolding minP_def using containment finite_odd odd_non_empty by metis
    then show ?thesis unfolding odd_def by auto
  qed
  ultimately show "False" by simp
qed

lemma minP_odd_upper_bound_restrict :
  assumes odd_le_even : "minP odd \<le> minP even"
  shows "minP odd \<le> N"
proof (rule ccontr)
  assume "\<not>(minP odd \<le> N)"
  then have minP_value : "minP odd = N + 1" 
    using minP_odd_upper_bound by simp
  then have "N + 1 \<in> {i |i. i \<in> odd \<and> P i}" 
    unfolding minP_def using containment finite_odd odd_non_empty  by metis
  then have "N + 1 \<in> odd" by simp
  then have "(N + 1) mod 2 = 1" unfolding odd_def by auto
  moreover have "(N + 1) mod 2 = 0"
  proof -
    have "minP even = N + 1" 
      using minP_even_upper_bound odd_le_even minP_value by simp
    then have "N + 1 \<in> {i |i. i \<in> even \<and> P i}" 
      unfolding minP_def using containment finite_even even_non_empty by metis
    then have "N + 1 \<in> even" by simp
    then show ?thesis unfolding even_def by auto
  qed
  ultimately show "False" by simp
qed

subsubsection \<open>Miscellaneous Proofs\<close>
text \<open>This section contains additional proofs which are useful in the final proof.\<close>
lemma ot_equals_N :
  assumes m_ot : "inv (ot s') odd" and ot_false : "ot s' \<noteq> minP odd"
  shows "ot s' = N"
  using assms unfolding inv_def by blast

lemma et_equals_N :
  assumes m_et : "inv (et s') even" and et_false : "et s' \<noteq> minP even"
  shows "et s' = N"
  using assms unfolding inv_def by blast

lemma expr_true_simp : "expr_eq b\<^sub>w true = {s. ec s < et s \<and> ec s < ot s}"
  unfolding expr_eq_def Bool_and_def Nat_less_than_def 
  by (simp add: Collect_mono true_Value_def)

lemma expr_false_simp : "expr_eq b\<^sub>w false = {s. ec s \<ge> et s \<or> ec s \<ge> ot s}"
  unfolding expr_eq_def Bool_and_def Nat_less_than_def 
  by (simp add: Collect_mono false_Value_def, auto)

lemma finite_wfr : "finite wfr\<^sub>w"
proof -
  have "wfr\<^sub>w \<subseteq> {(n, n'). n \<le> N + 1 \<and> n' \<le> N + 1}" by auto
  then show ?thesis using infinite_super by auto
qed

lemma wfr_ordered : "(x, y) \<in> wfr\<^sub>w\<^sup>+ \<Longrightarrow> x < y"
  by (induct rule:trancl.induct, auto)

lemma refl_1 : "refl g\<^sub>i"
  unfolding refl_on_def by blast

lemma stable_simp_1 : "stable p\<^sub>i r\<^sub>i" 
  unfolding stable_def by auto

lemma stable_simp_2 : "stable p\<^sub>1 r\<^sub>1"
  unfolding stable_def by auto

lemma stable_simp_3 : "stable p\<^sub>2 r\<^sub>2"
  unfolding stable_def by auto

lemma subset_1 : "p_inv \<triangleleft> ec_to_0 \<subseteq> p_inv \<triangleleft> UNIV \<triangleright> p_inv_ext"
  unfolding restrict_domain_def inv_loop_def even_def restrict_range_def by auto

lemma subset_2 : "((dec wfr\<^sub>w\<^sup>= v\<^sub>w) \<inter> q\<^sub>w\<^sup>*) \<triangleright> (p\<^sub>w \<inter> b1\<^sub>w) \<subseteq> e29_post"
  unfolding restrict_range_def by auto

lemma subset_3 : "b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k \<subseteq> c\<^sub>w_pre" by auto

lemma subset_4 : "e28_post \<subseteq> q1_25" by blast

lemma subset_5 : "ot_decreq \<inter> P' p_inv \<subseteq> ot_decreq" by blast

lemma subset_6 : "r\<^sub>w \<subseteq> {(s, s'). ec s' = ec s \<and> et s' = et s}" by auto

lemma subset_7 : "{(s, s'). ot s' = N \<and> et s' = N} \<subseteq> UNIV \<triangleright> p_inv"
  unfolding inv_def restrict_range_def by blast

lemma subset_8 : "q1_25 \<inter> q2_25 \<subseteq> s24_first_post" by auto

lemma equality_1 : "{(s, s'). et s' = et s \<and> ot s' = ot s} \<inter> 
      {(s, s'). s \<in> p_inv \<longrightarrow> s' \<in> p_inv} = {(s, s'). et s' = et s \<and> ot s' = ot s}" 
  by auto

lemma equality_2 : "no_change \<union> (ot_decreq \<inter> P' p_inv) = ot_decreq \<inter> P' p_inv" by auto

lemma equality_3 : "no_change \<union> (et_decreq \<inter> P' p_inv) = et_decreq \<inter> P' p_inv" by auto

lemma change_t : "y\<lparr>t := (t x)\<rparr> = x \<Longrightarrow> et x = et y \<and> ot x = ot y"
  by (metis ext_inject surjective update_convs(1))

lemma change_et : "y\<lparr>et := et x\<rparr> = x \<Longrightarrow> ot x = ot y \<and> 
      ec x = ec y \<and> oc x = oc y"
  by (metis ext_inject surjective update_convs(2))

lemma change_ot: "y\<lparr>ot := ot x\<rparr> = x \<Longrightarrow> et x = et y"
  by (metis ext_inject surjective update_convs(3))

lemma change_ec : "y\<lparr>ec := ec x\<rparr> = x \<Longrightarrow> et x = et y \<and> ot x = ot y \<and> 
      oc x = oc y \<and> t x = t y"
  by (metis ext_inject surjective update_convs(4))

lemma refinement_1 : "guar_inv p_inv \<iinter> guar(et_decreq \<inter> P' p_inv) \<ge> 
      guar (et_decreq \<inter> P' p_inv)"
proof -
  have "P' p_inv \<inter> (et_decreq \<inter> P' p_inv) = et_decreq \<inter> P' p_inv" by fast
  then show ?thesis 
    unfolding guar_inv_def using guar_merge order_refl by (metis (no_types, lifting))
qed

lemma refinement_2 : "guar_inv p_inv \<iinter> guar(ot_decreq \<inter> P' p_inv) \<ge> 
      guar(ot_decreq \<inter> P' p_inv)" 
proof -
  have "P' p_inv \<inter> (ot_decreq \<inter> P' p_inv) = ot_decreq \<inter> P' p_inv" by fast
  then show ?thesis 
    unfolding guar_inv_def using guar_merge order_refl by (metis (no_types, lifting))
qed

lemma refinement_3 : "guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> 
      \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr> \<ge> 
      guar(et_decreq \<inter> P' p_inv) \<iinter> ( (rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>) ;
      ( rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr> ) )"
proof -
  have "guar g\<^sub>c \<iinter> (rely r\<^sub>c \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;(\<lbrace>p\<^sub>w\<rbrace>;\<lparr>q1_25\<rparr>)) \<ge> 
        guar g\<^sub>c \<iinter> (rely r\<^sub>c \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>);(rely r\<^sub>c \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>)"
    using conj.sync_mono_right rely_seq_distrib by presburger
  then show ?thesis
    by (simp add: local.conj_assoc seq_assoc)
qed

lemma element_argument_1 :
  fixes k\<^sub>a
  assumes "(s, s') \<in> (b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<^sub>a) \<triangleleft> ((r\<^sub>w \<union> g\<^sub>w)\<^sup>* \<inter> c\<^sub>w_post)"
  shows "(s, s') \<in> q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> fn_less v\<^sub>w wfr\<^sub>w k\<^sub>a)"
proof -
  have "s' \<in> p\<^sub>w"
  proof -
    have "(s, s') \<in> (P' p_inv \<inter> (ot_decreq \<union> et_decreq))\<^sup>*" 
      using assms unfolding restrict_domain_def by (simp add: inf_commute inf_sup_distrib1)
    then have "(s, s') \<in> P' p_inv" 
      by (induction, auto)
    then show ?thesis using assms unfolding restrict_domain_def by blast
  qed
  moreover have "s' \<in> fn_less v\<^sub>w wfr\<^sub>w k\<^sub>a"
  proof -
    have "k\<^sub>a \<le> N + 1"
    proof (rule ccontr)
      assume assm : "\<not>(k\<^sub>a \<le> N + 1)"
      have "et s \<le> N + 1" 
        using assms minP_even_upper_bound et_equals_N 
        unfolding restrict_domain_def by fastforce
      then show "False" using assm assms unfolding restrict_domain_def fn_less_def by auto
    qed
    then show ?thesis using assms unfolding restrict_domain_def fn_less_def by auto
  qed
  ultimately show ?thesis 
    unfolding restrict_range_def by auto
qed

lemma element_argument_2 :
  assumes "P(ec s) \<and> ec s < et s \<and> 
        inv_loop (ec s) (et s) even \<and> inv (et s) even \<and> 
        ec s = k \<and> et s' = ec s \<and>
        ot s = ot s' \<and> ec s = ec s' \<and> oc s = oc s'"
  shows "(s, s') \<in> g\<^sub>1"
proof -
  have "et s' = minP even" using assms unfolding minP_def inv_loop_def
    using even_non_empty finite_even by (auto, simp add: le_antisym)
  then show ?thesis unfolding inv_def using assms by auto
qed

lemma element_argument_3 :
  assumes "P(ec s) \<and> ec s < et s \<and> 
        inv_loop (ec s) (et s) even \<and> inv (et s) even \<and> 
        ec s = k \<and> et s' = ec s \<and>
        ot s = ot s' \<and> ec s = ec s' \<and> oc s = oc s'"
 shows "(s, s') \<in> q\<^sub>1"
  using assms unfolding inv_loop_def by auto

lemma element_argument_4 :
  assumes "\<not>(P(ec s)) \<and> ec s < et s \<and> 
        inv_loop (ec s) (et s) even \<and> inv (et s) even \<and> 
        ec s + 2 = k \<and> ec s' = ec s + 2 \<and>
        et s = et s' \<and> ot s = ot s' \<and> oc s = oc s'"
  shows "(s, s') \<in> g\<^sub>2"
  using assms unfolding inv_loop_def by auto

lemma element_argument_5 :
  assumes "\<not>(P(ec s)) \<and> ec s < et s \<and> 
        inv_loop (ec s) (et s) even \<and> inv (et s) even \<and> 
        ec s + 2 = k \<and> ec s' = ec s + 2 \<and>
        et s = et s' \<and> ot s = ot s' \<and> oc s = oc s'"
  shows "(s, s') \<in> q\<^sub>2"
proof -
  have "inv_loop (ec s') (et s') even"
  proof -
    have "ec s' \<le> minP even"
    proof -
      have "\<forall>x. x < ec s \<longrightarrow> x \<notin> {i |i. i \<in> even \<and> P i}" 
        using assms even_non_empty finite_even unfolding inv_loop_def minP_def by auto
      moreover have "ec s + 1 \<notin> {i |i. i \<in> even \<and> P i}"
        using assms unfolding even_def inv_loop_def by fastforce
      moreover have "{x. x < ec s + 2} = 
            {x. x < ec s \<or> x = ec s \<or> x = ec s + 1}" by auto
      ultimately have "\<forall>x. x < ec s + 2 \<longrightarrow> x \<notin> {i |i. i \<in> even \<and> P i}" 
        using assms by auto
      then show ?thesis unfolding minP_def 
        using assms finite_even even_non_empty by (auto, meson Min_eq_iff not_le)
    qed
    then show ?thesis using assms minP_even_upper_bound 
      unfolding even_def inv_loop_def by auto
  qed
  then show ?thesis using assms by auto
qed

lemma if_assign_1_step : "\<And>k. (p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> g\<^sub>1 \<inter> q\<^sub>1" 
proof -
  fix k
  have "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> 
        {(s, s'). P(ec s) \<and> ec s < et s \<and> 
        inv_loop (ec s) (et s) even \<and> inv (et s) even \<and> 
        ec s = k \<and> et s' = ec s \<and>
        ot s = ot s' \<and> ec s = ec s' \<and> oc s = oc s'}" 
    unfolding update_def var_eq_def id_bar_def (* bulk_set_vars_def *) restrict_domain_def 
      restrict_range_def using change_et  sorry (* by auto *)
  also have "... \<subseteq> g\<^sub>1 \<inter> q\<^sub>1" 
    using element_argument_2 element_argument_3 by blast
  finally show "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> g\<^sub>1 \<inter> q\<^sub>1" by simp
qed

lemma if_assign_2_step : "\<And>k. (p\<^sub>2 \<inter> expr_eq e\<^sub>2 k) \<triangleleft> update Vec k \<subseteq> g\<^sub>2 \<inter> q\<^sub>2"
proof -
  fix k
  have "(p\<^sub>2 \<inter> expr_eq e\<^sub>2 k) \<triangleleft> update Vec k \<subseteq> 
        {(s, s'). \<not>(P(ec s)) \<and> ec s < et s \<and> 
        inv_loop (ec s) (et s) even \<and> inv (et s) even \<and> 
        ec s + 2 = k \<and> ec s' = ec s + 2 \<and>
        et s = et s' \<and> ot s = ot s' \<and> oc s = oc s'}" 
    unfolding var_eq_def id_bar_def (* bulk_set_vars_def *) restrict_domain_def 
      restrict_range_def using change_ec sorry (* by auto *)
  also have "... \<subseteq> g\<^sub>2 \<inter> q\<^sub>2" 
    using element_argument_4 element_argument_5 by blast
  finally show "(p\<^sub>2 \<inter> expr_eq e\<^sub>2 k) \<triangleleft> update Vec k \<subseteq> g\<^sub>2 \<inter> q\<^sub>2" by simp
qed

subsubsection \<open>Major Proofs\<close>
text \<open>This section contains large proofs which are important to the final proof.\<close>
lemma step_29_argument : 
  assumes "(s, s') \<in> p_inv \<triangleleft> e29_post \<triangleright> p_inv"
  shows "(s, s') \<in> e28_post"
proof (cases "ec s' \<ge> ot s'")
  case True
  then show ?thesis using assms 
    unfolding inv_loop_def restrict_range_def restrict_domain_def by auto
next
  case f1 : False
  show ?thesis
  proof (cases "et s' = minP even")
    case True
    then show ?thesis using True assms 
      unfolding restrict_range_def restrict_domain_def by auto
  next
    case f2 : False
    show ?thesis 
    proof (cases "N \<in> even")
      case True
      have "N + 1 \<notin> even" using True unfolding even_def by auto
      then have "minP even \<noteq> N + 1" 
        unfolding minP_def using even_non_empty finite_even Min_eq_iff by auto
      then show ?thesis using assms minP_even_upper_bound f1 f2 
        unfolding inv_loop_def inv_def restrict_range_def restrict_domain_def by auto
    next
      case False
      then show ?thesis using assms f1 f2 minP_even_upper_bound minP_odd_upper_bound
        unfolding inv_loop_def inv_def restrict_range_def restrict_domain_def by auto
    qed
  qed
qed

lemma s30_step : "\<And>k. guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> 
          \<lbrace>b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<rbrace> ; \<lparr>q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> fn_less v\<^sub>w wfr\<^sub>w k)\<rparr> \<ge> c\<^sub>w"
proof -
  fix k
  have "guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> 
        \<lbrace>b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<rbrace> ; \<lparr> q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> fn_less v\<^sub>w wfr\<^sub>w k)\<rparr> \<ge> 
         guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> \<lbrace>b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<rbrace> ; \<lparr> c\<^sub>w_post\<rparr>"
          (is "_ \<ge> ?rhs")
  proof -
    have "(b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k) \<triangleleft> ( (r\<^sub>w \<union> g\<^sub>w)\<^sup>* \<inter> c\<^sub>w_post ) \<subseteq>
      q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> fn_less v\<^sub>w wfr\<^sub>w k)" using element_argument_1 by auto
    then have "\<lbrace>(b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k)\<rbrace>;
          \<lparr>q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> fn_less v\<^sub>w wfr\<^sub>w k)\<rparr> \<ge>
          \<lbrace>(b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k)\<rbrace>;\<lparr>( (r\<^sub>w \<union> g\<^sub>w)\<^sup>* \<inter> c\<^sub>w_post )\<rparr>" 
      using spec_strengthen seq_mono_right spec_strengthen spec_strengthen_under_pre by presburger
    then have "guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> \<lbrace>b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<rbrace>;
          \<lparr>q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> fn_less v\<^sub>w wfr\<^sub>w k)\<rparr> \<ge>
          guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> \<lbrace>b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<rbrace>;
          \<lparr>(r\<^sub>w \<union> g\<^sub>w)\<^sup>* \<inter> c\<^sub>w_post\<rparr>" using conj.sync_mono_right by blast
    moreover have "... \<ge> guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> 
          \<lbrace>b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<rbrace> ; \<lparr>c\<^sub>w_post\<rparr>"
      using conj.sync_mono_right move_pre conj.sync_assoc order_refl conj.left_commute 
        spec_trading_refinement seq_mono_right conj.sync_mono_right 
        order_refl conj.left_idem pre_spec_trading calculation local.conj_commute 
      by (smt (verit, best)) 
    ultimately show ?thesis by auto
  qed
  also have "?rhs \<ge> rely r\<^sub>w \<iinter> guar g\<^sub>w \<iinter>  \<lbrace>c\<^sub>w_pre\<rbrace> ; \<lparr> c\<^sub>w_post\<rparr>"
    using conj.sync_mono_right seq_mono_left conj.sync_commute subset_3 assert_iso by force
  show "guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> 
        \<lbrace>b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<rbrace> ; \<lparr>q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> fn_less v\<^sub>w wfr\<^sub>w k)\<rparr> \<ge> c\<^sub>w" 
    by (smt (verit) assert_iso assert_redundant assert_seq_self calculation
        local.conj_commute move_pre seq_assoc seq_mono subset_3)
qed

lemma s30_while_refinement : "guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> 
      \<lbrace>p\<^sub>w\<rbrace> ; \<lparr> ((dec wfr\<^sub>w\<^sup>= v\<^sub>w) \<inter> q\<^sub>w\<^sup>*) \<triangleright> (p\<^sub>w \<inter> b1\<^sub>w)\<rparr> \<ge> While b\<^sub>w do c\<^sub>w od"
proof -
  have g_reflexive : "refl g\<^sub>w" unfolding refl_on_def by auto
  moreover have wellfounded : "wf wfr\<^sub>w" 
    using finite_acyclic_wf unfolding acyclic_def using wfr_ordered finite_wfr by blast  
  moreover have wfr_trans : "trans wfr\<^sub>w" using trans_def by fastforce
  moreover have single_reference_b : "single_reference b\<^sub>w r\<^sub>w" 
    using estable_def eval.simps(2) by fastforce
  moreover have tolerate_interference: "tolerates_interference p\<^sub>w (q\<^sub>w\<^sup>* \<triangleright> p\<^sub>w) r\<^sub>w"
    unfolding tolerates_interference_def stable_def 
      restrict_range_def restrict_domain_def by auto
  moreover have b_boolean : "p\<^sub>w \<subseteq> expr_type b\<^sub>w boolean" 
    unfolding expr_type_def using expr_false_simp expr_true_simp by auto
  moreover have pb_establishes_b0 :  "p\<^sub>w \<inter> expr_eq b\<^sub>w true \<subseteq> b0\<^sub>w" 
    using expr_true_simp by blast
  moreover have pr_maintains_b0: "stable b0\<^sub>w (p\<^sub>w \<triangleleft> r\<^sub>w)"
    unfolding stable_def restrict_domain_def by auto
  moreover have pnegb_establishes_b1: "p\<^sub>w \<inter> expr_eq b\<^sub>w false \<subseteq> b1\<^sub>w" 
    using expr_false_simp by auto
  moreover have pr_maintains_b1: "stable b1\<^sub>w (p\<^sub>w \<triangleleft> r\<^sub>w)"
    unfolding stable_def restrict_domain_def by auto
  moreover have pr_variant: "p\<^sub>w \<triangleleft> r\<^sub>w \<subseteq> (dec wfr\<^sub>w\<^sup>= v\<^sub>w)" 
    unfolding restrict_domain_def dec_variant_def by auto
  moreover have step: "\<And>k. guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> 
        \<lbrace>b0\<^sub>w \<inter> p\<^sub>w \<inter> fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<rbrace> ; \<lparr>q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> fn_less v\<^sub>w wfr\<^sub>w k)\<rparr> \<ge> c\<^sub>w" 
    using s30_step by blast
  ultimately show ?thesis using rely_loop by blast
qed

lemma s32_if_refinement : "rely r\<^sub>i \<iinter> \<lbrace>p\<^sub>i\<rbrace> ; \<lparr>q\<^sub>i\<rparr> \<ge> If b\<^sub>i then (rely r\<^sub>i \<iinter> \<lbrace>b0\<^sub>i \<inter> p\<^sub>i\<rbrace> ; \<lparr> q\<^sub>i\<rparr>) 
      else (rely r\<^sub>i \<iinter> \<lbrace>b1\<^sub>i \<inter> p\<^sub>i\<rbrace> ; \<lparr>q\<^sub>i\<rparr>) fi"
proof -
  have single_reference_b: "single_reference b\<^sub>i r\<^sub>i" by simp
  moreover have tolerate_interference: "tolerates_interference p\<^sub>i q\<^sub>i r\<^sub>i"
    unfolding tolerates_interference_def restrict_domain_def using stable_simp_1 by auto
  moreover have b_boolean: "p\<^sub>i \<subseteq> expr_type b\<^sub>i boolean" 
    unfolding expr_type_def expr_eq_def false_Value_def true_Value_def by auto
  moreover have pb_establishes_b0: "p\<^sub>i \<inter> expr_eq b\<^sub>i true \<subseteq> b0\<^sub>i" 
    by (simp add: expr_eq_def true_Value_def)
  moreover have pr_maintains_b0: "stable b0\<^sub>i (p\<^sub>i \<triangleleft> r\<^sub>i)"
    unfolding stable_def restrict_domain_def by auto
  moreover have pnegb_establishes_b1: "p\<^sub>i \<inter> expr_eq b\<^sub>i false \<subseteq> b1\<^sub>i" 
    by (simp add: expr_eq_def false_Value_def)
  moreover have pr_maintains_b1: "stable b1\<^sub>i (p\<^sub>i \<triangleleft> r\<^sub>i)"
    unfolding stable_def restrict_domain_def by auto
  ultimately show ?thesis using rely_conditional by blast
qed

subsubsection \<open>Assignment Proofs\<close>

text \<open>This section contains proofs of refinements of specifications to assignments.\<close>

lemma initial_assignment_et : "rely {(s, s'). s' = s} \<iinter> \<lparr>{(s, s'). et s' = N}\<rparr> \<ge>
      Vet::= Constant N"
proof -
  have "rely{(s, s'). s' = s} \<iinter> \<lparr>{(s, s'). et s' = N}\<rparr> \<ge> 
        rely r\<^sub>e \<iinter> guar g\<^sub>e \<iinter> \<lbrace>p\<^sub>e\<rbrace> ; Vet:\<^sub>f\<lparr>q\<^sub>e\<rparr>" ( is "_ \<ge> ?rhs")
    using assert_top conj.sync_mono_right guar_introduce rely_def3 
      var_frame_def rely_guar_def seq_nil_left var_frame_expand by presburger
  also have "?rhs \<ge> Vet ::= e\<^sub>e"
  proof -
    have refl_g : "refl g\<^sub>e" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>e r\<^sub>e" by simp
    moreover have estable_e: "estable e\<^sub>e r\<^sub>e" by (simp add: stable_expression_constant)
    moreover have tolerate: "tolerates_interference p\<^sub>e q\<^sub>e r\<^sub>e"
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
    moreover have req_g: "\<And>k. (p\<^sub>e \<inter> expr_eq e\<^sub>e k) \<triangleleft> update Vet k \<subseteq> g\<^sub>e" by simp
    moreover have req_q: "\<And>k. (p\<^sub>e \<inter> expr_eq e\<^sub>e k) \<triangleleft> update Vet k \<subseteq> q\<^sub>e"
    proof -
      fix k
      have update_q: "update Vet k \<subseteq> q\<^sub>e"
        unfolding restrict_domain_def using update_eq sorry 
      show "(p\<^sub>e \<inter> expr_eq e\<^sub>e k) \<triangleleft> update Vet k \<subseteq> q\<^sub>e" 
        by (simp add: inf.coboundedI1 inf_commute restrict_domain_def update_q) 
    qed
    ultimately show ?thesis using local_expr_assign by presburger
  qed
  finally show ?thesis .
qed

lemma initial_assignment_ot : "rely{(s, s'). s' = s} \<iinter> 
      \<lparr>{(s, s'). et s' = et s \<and> ot s' = N}\<rparr> \<ge> Vot::= Constant N"
proof -
  have "rely{(s, s'). s' = s} \<iinter> \<lparr>{(s, s'). et s' = et s \<and> ot s' = N}\<rparr> \<ge> 
        rely r\<^sub>o \<iinter> guar g\<^sub>o \<iinter> \<lbrace>p\<^sub>o\<rbrace> ; Vot:\<^sub>f\<lparr>q\<^sub>o\<rparr>" (is "_ \<ge> ?rhs")
    using assert_top conj.sync_mono_right guar_introduce rely_def3 rely_guar_def 
      var_frame_def seq_nil_left var_frame_expand by presburger
  also have "?rhs \<ge> Vot ::= e\<^sub>o"
  proof -
    have "refl g\<^sub>o" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>o r\<^sub>o" by simp
    moreover have estable_e: "estable e\<^sub>e r\<^sub>e"by (simp add: stable_expression_constant)
    moreover have tolerate: "tolerates_interference p\<^sub>o q\<^sub>o r\<^sub>o"
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
    moreover have req_g: "\<And>k. (p\<^sub>o \<inter> expr_eq e\<^sub>o k) \<triangleleft> update Vot k \<subseteq> g\<^sub>o" by simp
    moreover have req_q: "\<And>k. (p\<^sub>o \<inter> expr_eq e\<^sub>o k) \<triangleleft> update Vot k \<subseteq> q\<^sub>o"
      unfolding restrict_domain_def restrict_range_def id_bar_def var_eq_def 
      using change_ot  sorry 
    ultimately show ?thesis using local_expr_assign by presburger 
  qed
  finally show ?thesis .
qed

lemma initial_assignment : "var_init \<ge> Vet ::= Constant N ; Vot::= Constant N"
proof -
  have "relcomp {(s, s'). et s' = N} {(s, s'). et s' = et s \<and> ot s' = N} \<subseteq> 
        {(s, s'). ot s' = N \<and> et s' = N}" by auto
  then have "\<lparr>{(s, s'). ot s' = N \<and> et s' = N}\<rparr> \<ge> 
        \<lparr>{(s, s'). et s' = N}\<rparr> ; \<lparr>{(s, s'). et s' = et s \<and> ot s' = N}\<rparr>" 
    using spec_chain by blast
  then have "var_init \<ge> rely{(s, s'). s' = s} \<iinter> 
        \<lparr>{(s, s'). et s' = N}\<rparr> ; \<lparr>{(s, s'). et s' = et s \<and> ot s' = N}\<rparr>"
          (is "_ \<ge> ?rhs")
    by (simp add: conj.sync_mono_right)
  also have "?rhs \<ge> (rely{(s, s'). s' = s} \<iinter> \<lparr>{(s, s'). et s' = N}\<rparr>) ;
        (rely{(s, s'). s' = s} \<iinter> \<lparr>{(s, s'). et s' = et s \<and> ot s' = N}\<rparr>)" 
          (is "_ \<ge> ?rhs")
    using rely_seq_distrib by blast
  also have "?rhs \<ge> Vet::= Constant N ; Vot::= Constant N" 
    using initial_assignment_ot initial_assignment_et seq_mono by blast
  finally show ?thesis by auto
qed

lemma assign_ec : "var_init_ec \<ge> Vec::= Constant 0"
proof -
  have "var_init_ec \<ge> guar g\<^sub>c \<iinter> rely r\<^sub>c \<iinter> \<lbrace>p\<^sub>c\<rbrace>; Vec:\<^sub>f\<lparr>q\<^sub>c\<rparr>" (is "_ \<ge> ?rhs")
    using conj.sync_mono_right guar_introduce seq_mono_right var_frame_def 
          var_frame_expand by presburger
  also have "?rhs \<ge> rely r\<^sub>c \<iinter> guar g\<^sub>c \<iinter> \<lbrace>p\<^sub>c\<rbrace> ; Vec:\<^sub>f\<lparr>q\<^sub>c\<rparr>" (is "_ \<ge> ?rhs")
    using conj.sync_commute conj_assoc by auto
  also have "?rhs \<ge> Vec::= e\<^sub>c"
  proof -
    have refl: "refl g\<^sub>c" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>c r\<^sub>c" by simp
    moreover have estable_e: "estable e\<^sub>c r\<^sub>c" by (simp add: stable_expression_constant)
    moreover have tolerate: "tolerates_interference p\<^sub>c q\<^sub>c r\<^sub>c"
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
    moreover have req_g: "\<And>k. (p\<^sub>c \<inter> expr_eq e\<^sub>c k) \<triangleleft> update Vec k \<subseteq> g\<^sub>c"  sorry
    moreover have req_q: "\<And>k. (p\<^sub>c \<inter> expr_eq e\<^sub>c k) \<triangleleft> update Vec k \<subseteq> q\<^sub>c" 
    proof -
      fix k
      have "update Vec k \<subseteq> {(s,s'). et s = et s' }" using update_nochange  sorry
      have "update Vec k \<subseteq> 
            {(s,s'). et s = et s' \<and> ot s = ot s' \<and> oc s = oc s' \<and> t s = t s' }"
        using change_ec  sorry 
      then show "(p\<^sub>c \<inter> expr_eq e\<^sub>c k) \<triangleleft> update Vec k \<subseteq> q\<^sub>c"
        unfolding restrict_domain_def update_def  sorry 
    qed
    ultimately show ?thesis using local_expr_assign by presburger
  qed
  finally show ?thesis by blast
qed

lemma post_assignment : "post_assign_t \<ge> Vt::= e\<^sub>t"
proof -
  have "post_assign_t \<ge> rely r\<^sub>t \<iinter> guar g\<^sub>t \<iinter> \<lbrace>p\<^sub>t\<rbrace> ; Vt:\<^sub>f\<lparr>q\<^sub>t\<rparr>" (is "_ \<ge> ?rhs")
    using assert_top conj.sync_commute conj.sync_mono_right guar_introduce seq_nil_left 
          var_frame_def by (metis (no_types, lifting) var_frame_expand)
  also have "?rhs \<ge> Vt::= e\<^sub>t"
  proof -
    have "refl g\<^sub>t" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>t r\<^sub>t" using estable_def by fastforce
    moreover have estable_e: "estable e\<^sub>t r\<^sub>t" 
    proof -
      have estable_et: "estable (Variable et) r\<^sub>t" 
        by (simp add: stable_expression_variable) 
      have estable_ot: "estable (Variable ot) r\<^sub>t"
        by (simp add: stable_expression_variable) 
      show ?thesis using estable_et estable_ot stable_expression_binaryop by blast 
    qed
    moreover have tolerate: "tolerates_interference p\<^sub>t q\<^sub>t r\<^sub>t"  
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
    moreover have req_g: "\<And>k. (p\<^sub>t \<inter> expr_eq e\<^sub>t k) \<triangleleft> update Vt k \<subseteq> g\<^sub>t"
    proof -
      fix k
      have "{(s, s'). (s, s') \<in> id_bar{Vt}} \<subseteq> {(s,s'). et s = et s' \<and> ot s = ot s'}"
        using change_t  sorry  
      then show "(p\<^sub>t \<inter> expr_eq e\<^sub>t k) \<triangleleft> update Vt k \<subseteq> g\<^sub>t" 
        unfolding restrict_domain_def restrict_range_def id_bar_def var_eq_def sorry
      qed
    moreover have req_q: "\<And>k. (p\<^sub>t \<inter> expr_eq e\<^sub>t k) \<triangleleft> update Vt k \<subseteq> q\<^sub>t"
    proof -
      fix k
      have "{(s,s'). (s,s') \<in> id_bar{Vt}} \<subseteq> {(s,s'). et s = et s' \<and> ot s = ot s'}"
        using change_t  sorry 
      then show "(p\<^sub>t \<inter> expr_eq e\<^sub>t k) \<triangleleft> update Vt k \<subseteq> q\<^sub>t" 
        unfolding restrict_domain_def restrict_range_def id_bar_def var_eq_def sorry
      qed
    ultimately show ?thesis using local_expr_assign by presburger 
  qed
  finally show ?thesis .
qed

lemma if_assign_1 : "if1 \<ge> Vet::= e\<^sub>1"
proof -
  have "if1 \<ge> rely r\<^sub>1 \<iinter> guar g\<^sub>1 \<iinter> \<lbrace>p\<^sub>1\<rbrace> ; Vet:\<^sub>f\<lparr>q\<^sub>1\<rparr>" (is "_ \<ge> ?rhs")
    using guar_introduce var_frame_def conj.sync_commute conj.sync_mono_right
          seq_mono_right var_frame_expand by presburger
  also have "?rhs \<ge> Vet::= e\<^sub>1"
  proof -
    have "refl g\<^sub>1" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>1 r\<^sub>1" using estable_def by fastforce
    moreover have estable_e: "estable e\<^sub>1 r\<^sub>1" by (simp add: stable_expression_variable) 
    moreover have tolerate: "tolerates_interference p\<^sub>1 q\<^sub>1 r\<^sub>1"
      unfolding tolerates_interference_def restrict_domain_def using stable_simp_2 by auto
    moreover have assign: "\<And>k. (p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> g\<^sub>1" 
    proof -
      fix k
      have a: "p\<^sub>1 \<subseteq> {s. P(ec s) \<and> ec s < et s \<and> inv_loop (ec s) (et s) even \<and> inv (et s) even}"
        by force 
      have b: "expr_eq e\<^sub>1 k \<subseteq> {s. ec s = k}"
        by (simp add: expr_eq_def) 
      have c: "p\<^sub>1 \<inter> expr_eq e\<^sub>1 k \<subseteq> 
        {s. P(ec s) \<and> ec s < et s \<and> inv_loop (ec s) (et s) even \<and> inv (et s) even \<and> ec s = k}"
        using a b by blast 
      have d: "update Vet k \<subseteq> {(s,s'). ec s = ec s' \<and> ot s = ot s'}" sorry 
      have a: "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> 
        {s. P(ec s) \<and> ec s < et s \<and> inv_loop (ec s) (et s) even \<and> inv (et s) even \<and> ec s = k} \<triangleleft>
           {(s,s'). ec s = ec s' \<and> ot s = ot s' }" sorry
      have ec_lt_et: "p\<^sub>1 \<inter> expr_eq e\<^sub>1 k \<subseteq> {s. ec s \<le> et s}" sorry
      have et_k: "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> {(s,s'). et s' = ec s'}" sorry 
      have ga: "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> et_decreq" sorry 
      have gb: "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> P' p_inv" sorry
      show "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> g\<^sub>1" 
        using ga gb by force
    qed
    moreover have assign: "\<And>k. (p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> q\<^sub>1"
    proof -
      fix k
      have q1: "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> {(s, s'). inv_loop (ec s') (et s') even \<and> 
        0 \<le> 1 + et s' - ec s' \<and> et s' - ec s' < et s - ec s}" sorry
      show "(p\<^sub>1 \<inter> expr_eq e\<^sub>1 k) \<triangleleft> update Vet k \<subseteq> q\<^sub>1" using q1 by blast 
    qed
    ultimately show ?thesis using local_expr_assign by presburger
  qed
  finally show ?thesis by simp
qed

lemma if_assign_2 : "if2 \<ge> Vec::= e\<^sub>2"
proof -               
  have "if2 \<ge> rely r\<^sub>2 \<iinter> guar g\<^sub>2 \<iinter> \<lbrace>p\<^sub>2\<rbrace> ; Vec:\<^sub>f\<lparr>q\<^sub>2\<rparr>" (is "_ \<ge> ?rhs")
    using guar_introduce var_frame_def conj.sync_commute conj.sync_mono_right seq_mono_right
          var_frame_expand by presburger 
  also have "?rhs \<ge> Vec::= e\<^sub>2"
  proof -
    have "refl g\<^sub>2" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>2 r\<^sub>2" using estable_def by fastforce
    moreover have estable_e: "estable e\<^sub>2 r\<^sub>2" by (simp add: stable_expression_variable) 
    moreover have tolerate: "tolerates_interference p\<^sub>2 q\<^sub>2 r\<^sub>2" 
      unfolding tolerates_interference_def restrict_domain_def using stable_simp_3 by auto
    moreover have assign: "\<And>k. (p\<^sub>2 \<inter> expr_eq e\<^sub>2 k) \<triangleleft> update Vec k \<subseteq> g\<^sub>2"
      using if_assign_2_step by auto
    moreover have assign: "\<And>k. (p\<^sub>2 \<inter> expr_eq e\<^sub>2 k) \<triangleleft> update Vec k \<subseteq> q\<^sub>2"
      using if_assign_2_step by auto
    ultimately show ?thesis using local_expr_assign by presburger 
  qed
  finally show ?thesis by fastforce
qed

subsubsection \<open>Even Refinement\<close>
text \<open>This section contains the refinement of the even thread as described 
in section 4.3 of \cite{AGTRGT}.\<close>
lemma even_refinement : "guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> 
      \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> Vec ::= Constant 0 ; 
      While b\<^sub>w do If b\<^sub>i then Vet::= e\<^sub>1 else Vec::= e\<^sub>2 fi od"
proof -
  have step_28 : "guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> 
        Vec::= Constant 0;
        (guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr>)"
          (is "_ \<ge> ?rhs")
  proof -
    have "q1_25 = relcomp UNIV q1_25" by auto
    then have "\<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>UNIV\<rparr>;\<lparr>q1_25\<rparr>" (is "_ \<ge> ?rhs")
      using spec_chain seq_mono_right seq_assoc by auto
    also have "?rhs \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>p_inv \<triangleleft> UNIV\<rparr>;\<lparr>q1_25\<rparr>" (is "_ \<ge> ?rhs")
      using assert_restricts_spec by fastforce 
    also have "?rhs \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>p_inv \<triangleleft> UNIV \<triangleright> p_inv_ext\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" (is "_ \<ge> ?rhs")
      using seq_mono_right seq_assoc test_seq_assert test_seq_refine assert_restricts_spec
            seq_mono_left spec_assert_restricts spec_term spec_univ by presburger 
    also have "?rhs \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>p_inv \<triangleleft> ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" (is "_ \<ge> ?rhs")
      using spec_strengthen subset_1 seq_mono_left seq_mono_right by auto
    also have "?rhs \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" (is "_ \<ge> ?rhs")
      using seq_mono_left assert_restricts_spec by auto 
    finally have "\<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" (is "_ \<ge> ?rhs")
      by simp
    then have "guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> 
          guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" (is "_ \<ge> ?rhs")
      using conj.sync_mono_right conj_assoc by fast
    also have "?rhs \<ge> guar(et_decreq \<inter> P' p_inv) \<iinter> 
          ( rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr> ) ;
          ( rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr> )" (is "_ \<ge> ?rhs")
      using refinement_3 by auto
    also have "?rhs \<ge> var_init_ec;
          ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr> )" 
             (is "_ \<ge> ?rhs")
      by (metis (no_types, lifting) conj.sync_assoc guar_distrib_seq)
    moreover have "?rhs \<ge> var_init_ec; 
          ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> )"
             (is "_ \<ge> ?rhs")
      using subset_4 conj.sync_mono_right seq_mono_right spec_strengthen by presburger 
    moreover have "?rhs \<ge> Vec::= Constant 0; 
          ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely (ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> )" 
      using assign_ec seq_mono_left by blast
    ultimately show ?thesis by auto
  qed
  also have step_29 : "?rhs \<ge> Vec::= Constant 0;
        (guar (et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr>)"
           (is "_ \<ge> ?rhs")
  proof -
    have r_implies_P' : "(ot_decreq \<inter> P' p_inv) \<subseteq> P' p_inv" by blast
    moreover have g_implies_P' : "(et_decreq \<inter> P' p_inv) \<subseteq> P' p_inv" 
      by blast
    moreover have refinement : "p_inv \<triangleleft> e29_post \<triangleright> p_inv \<subseteq> e28_post" 
      using step_29_argument by auto
    ultimately have "rely(ot_decreq \<inter> P' p_inv) \<iinter> guar(et_decreq \<inter> P' p_inv) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>e28_post\<rparr> \<ge> 
          rely (ot_decreq \<inter> P' p_inv) \<iinter> guar (et_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>e29_post\<rparr>" 
      using strengthen_under_invariant by presburger
    then have "\<lbrace>p_inv\<rbrace>;((rely (ot_decreq \<inter> P' p_inv)) \<iinter> 
          (guar (et_decreq \<inter> P' p_inv)) \<iinter> \<lparr>e28_post\<rparr>) \<ge>
          \<lbrace>p_inv\<rbrace>;( (rely (ot_decreq \<inter> P' p_inv)) \<iinter> 
          (guar (et_decreq \<inter> P' p_inv)) \<iinter> \<lparr>e29_post\<rparr> )" 
      using initial_assert_rely_generic by presburger
    moreover have "p_inv_ext \<subseteq> p_inv" 
      by blast
    ultimately have "\<lbrace>p_inv_ext\<rbrace>;(rely(ot_decreq \<inter> P' p_inv) \<iinter> 
          guar(et_decreq \<inter> P' p_inv) \<iinter> \<lparr>e28_post\<rparr>) \<ge> 
          \<lbrace>p_inv_ext\<rbrace>;(rely(ot_decreq \<inter> P' p_inv) \<iinter> guar(et_decreq \<inter> P' p_inv) \<iinter> \<lparr>e29_post\<rparr>)" 
      using pre_strengthen_both by blast
    then have "rely(ot_decreq \<inter> P' p_inv) \<iinter> guar(et_decreq \<inter> P' p_inv) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> \<ge> 
          rely(ot_decreq \<inter> P' p_inv) \<iinter> guar(et_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr>" 
      using initial_assert_rely_generic by metis
    then have "guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> \<ge> 
          guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr>" (is "_ \<ge> ?rhs") 
      using conj.sync_commute initial_assert_rely_generic by auto
    moreover have "?rhs \<ge> guar(et_decreq \<inter> P' p_inv) \<iinter> rely ot_decreq \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr>"
      using rely_weaken conj.sync_mono_left conj.sync_mono_right subset_5 by presburger
    ultimately show ?thesis using seq_mono_right by blast 
  qed
  also have step_30 : "?rhs \<ge> Vec::= Constant 0; While b\<^sub>w do c\<^sub>w od" (is "_ \<ge> ?rhs")
  proof -
    have "guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr> \<ge> 
          guar g\<^sub>w \<iinter> rely r\<^sub>w \<iinter> \<lbrace>p\<^sub>w\<rbrace> ; \<lparr> ((dec wfr\<^sub>w\<^sup>= v\<^sub>w) \<inter> q\<^sub>w\<^sup>*) \<triangleright> (p\<^sub>w \<inter> b1\<^sub>w)\<rparr>"
             (is "_ \<ge> ?rhs")
      using spec_strengthen subset_2 conj.sync_mono_right seq_mono_right by auto
    also have "?rhs \<ge> While b\<^sub>w do c\<^sub>w od" using s30_while_refinement by blast
    finally have "guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr> \<ge> While b\<^sub>w do c\<^sub>w od" by simp
    then show ?thesis using seq_mono_right by blast
  qed
  also have step_31 : "?rhs \<ge> Vec::= Constant 0 ; While b\<^sub>w do e31_loop od" (is "_ \<ge> ?rhs")
  proof -
    have "c\<^sub>w \<ge> e31_loop" 
      using rely_weaken subset_6 conj.sync_mono_right conj.sync_mono_left by presburger
    then show ?thesis using conj.sync_mono_right conj.sync_mono_left seq_mono_right while_mono
      by blast
  qed
  also have step_32 : "?rhs \<ge> Vec::= Constant 0 ; While b\<^sub>w do If b\<^sub>i then if1 else if2 fi od"
                         (is "_ \<ge> ?rhs")
  proof -
    have "e31_loop \<ge> guar g\<^sub>i \<iinter> rely r\<^sub>i \<iinter> \<lbrace>p\<^sub>i\<rbrace>;\<lparr>q\<^sub>i\<rparr>"  (is "_ \<ge> ?rhs")
      by (simp add: conj.sync_commute)
    also have "?rhs \<ge> guar g\<^sub>i \<iinter> If b\<^sub>i then (rely r\<^sub>i \<iinter> \<lbrace>b0\<^sub>i \<inter> p\<^sub>i\<rbrace> ; \<lparr> q\<^sub>i\<rparr>) 
          else (rely r\<^sub>i \<iinter> \<lbrace>b1\<^sub>i \<inter> p\<^sub>i\<rbrace> ; \<lparr>q\<^sub>i\<rparr>) fi" (is "_ \<ge> ?rhs")
      using s32_if_refinement conj.sync_mono_right 
      by (metis (no_types, lifting) conj.sync_assoc)
    also have "?rhs \<ge> If b\<^sub>i then if1 else if2 fi"  (is "_ \<ge> ?rhs")
      using refl_1 conj_assoc guar_conditional_distrib local.conj_assoc refl_1 by fastforce 
    finally have "e31_loop \<ge> ?rhs" by simp
    then show ?thesis using seq_mono_right while_mono by blast
  qed
  also have step_33 : "?rhs \<ge> Vec::= Constant 0;
        While b\<^sub>w do If b\<^sub>i then Vet ::= e\<^sub>1 else if2 fi od" (is "_ \<ge> ?rhs")
    using if_assign_1 if_mono_left seq_mono_right while_mono by blast
  also have step_34 : "?rhs \<ge> Vec::= Constant 0;
        While b\<^sub>w do If b\<^sub>i then Vet::= e\<^sub>1 else Vec::= e\<^sub>2 fi od" 
    using if_assign_2 if_mono_right seq_mono_right while_mono by blast
  finally show ?thesis by auto
qed

subsubsection \<open>Odd Refinement\<close>
text \<open>The proof of the odd thread is trivial given the proof of the even thread. 
A complete proof is unneccessary given the even thread proof and so is not included here.\<close>
lemma odd_refinement : "guar(ot_decreq \<inter> P' p_inv) \<iinter> rely(et_decreq \<inter> P' p_inv) \<iinter> 
      \<lbrace>p_inv\<rbrace>;\<lparr>q2_25\<rparr> \<ge> 
      Voc::= Constant 1 ; 
      While b\<^sub>w\<^sub>o do If b\<^sub>i\<^sub>o then Vot::= e\<^sub>1\<^sub>o else Voc::= e\<^sub>2\<^sub>o fi od" 
  sorry

subsubsection \<open>Final Proof\<close>
text \<open>This Section shows the final proof of the findP problem as described in section 4 of \cite{AGTRGT}.\<close>
theorem findP_proof : 
  shows "rely no_change \<iinter> \<lparr>{(s, s'). (t s') = minP nats}\<rparr> \<ge> 
  Vet::= Constant N ; Vot::= Constant N ;
  ((Vec::= Constant 0 ; While b\<^sub>w do If b\<^sub>i then Vet::= e\<^sub>1 else Vec::= e\<^sub>2 fi od) \<parallel>
   (Voc::= Constant 1 ; While b\<^sub>w\<^sub>o do If b\<^sub>i\<^sub>o then Vot::= e\<^sub>1\<^sub>o else Voc::= e\<^sub>2\<^sub>o fi od));
  Vt::= e\<^sub>t"
proof -
  have step_22: "rely no_change \<iinter> \<lparr>{(s, s'). (t s') = minP nats}\<rparr> \<ge> 
        Vet ::= Constant N ; Vot ::= Constant N;
        (guar_inv p_inv \<iinter> rely no_change \<iinter> 
        \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr>)" (is "_ \<ge> ?rhs")
  proof -
    have "{(s, s'). t s' = minP nats} = relcomp UNIV {(s, s'). t s' = minP nats}" 
      by auto
    then have "\<lparr>{(s, s'). t s' = minP nats}\<rparr> \<ge> \<lparr>UNIV\<rparr>;\<lparr>{(s, s'). t s' = minP nats}\<rparr>" 
                 (is "_ \<ge> ?rhs") 
      using spec_to_sequential by (smt (verit, best))
    also have "?rhs \<ge> \<lparr>UNIV \<triangleright> p_inv\<rparr>;
          \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr>" (is "_ \<ge> ?rhs")
      using seq_mono_right seq_assoc seq_mono_left 
      using spec_assert_restricts spec_term spec_univ by presburger 
    also have "?rhs \<ge> \<lparr>{(s, s'). ot s' = N \<and> et s' = N}\<rparr>;
          \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr>" (is "_ \<ge> ?rhs")
      using spec_strengthen seq_mono subset_7 by simp
    finally have "rely no_change \<iinter> \<lparr>{(s, s'). t s' = minP nats}\<rparr> \<ge> 
          rely no_change \<iinter> ( \<lparr>{(s, s'). ot s' = N \<and> et s' = N}\<rparr>;
          \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr> )"  (is "_ \<ge> ?rhs")
      using conj.sync_mono_right by simp
    also have "?rhs \<ge> var_init; (rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr>)"
                 (is "_ \<ge> ?rhs")
      using rely_seq_distrib seq_assoc by auto
    also have "?rhs \<ge> var_init ; 
          (guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr>)"
             (is "_ \<ge> ?rhs")
      using conj.sync_mono_left guar_introduce guar_inv_def seq_mono_right by auto
    also have "?rhs \<ge> Vet::= Constant N ; Vot::= Constant N ;
          ( guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr> )" 
      using initial_assignment seq_mono_left by blast
    finally show ?thesis by simp
  qed
  also have step_23 : "?rhs \<ge> Vet::= Constant N ; Vot::= Constant N ; 
        ( guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr> )" (is "_ \<ge> ?rhs")
  proof -
    have r_implies_P' : "no_change \<subseteq> P' p_inv" by auto
    moreover have g_implies_P' : "P' p_inv \<subseteq> P' p_inv" by simp
    moreover have post_cond_implies : "p_inv \<triangleleft> s23_post \<triangleright> p_inv \<subseteq> 
          {(s, s'). t s' = minP nats}" 
      using minP_even_upper_bound minP_odd_upper_bound minP_even_upper_bound_restrict 
        et_equals_N ot_equals_N joining_minP even_union_odd 
        unfolding restrict_range_def restrict_domain_def by fastforce
    ultimately have "rely no_change \<iinter> guar_inv p_inv \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr> \<ge> 
          rely no_change \<iinter> guar_inv p_inv \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr>" 
      unfolding guar_inv_def using strengthen_under_invariant by auto
    then have "guar_inv p_inv \<iinter> rely no_change \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>{(s, s'). t s' = minP nats}\<rparr> \<ge> 
          guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr>" 
      using conj.sync_commute by presburger
    then show ?thesis using seq_mono_right by blast
  qed
  also have step_24 : "?rhs \<ge> Vet ::= Constant N ; Vot ::= Constant N ; 
        ( guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr> ) ;
        Vt::= e\<^sub>t" (is "_ \<ge> ?rhs")
  proof -
    have simp_to_post : "guar_inv p_inv \<iinter> rely no_change \<iinter> \<lparr>s24_second_post\<rparr> \<ge> 
          post_assign_t"
      unfolding guar_inv_def using guar_introduce conj.sync_mono_left 
        guar_merge equality_1 by (metis (no_types, lifting))
    have "( relcomp s24_first_post s24_second_post ) \<subseteq> s23_post" by auto
    then have "\<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr> \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr>;\<lparr>s24_second_post\<rparr>" 
      using spec_strengthen spec_chain seq_assoc seq_mono_right by presburger
    then have "( guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr> ) \<ge> 
          (guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr>;\<lparr>s24_second_post\<rparr>)"
             (is "_ \<ge> ?rhs")
      using conj.sync_mono_right by auto
    also have "?rhs \<ge> ( guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr> ) ;
          ( guar_inv p_inv \<iinter> rely no_change \<iinter> \<lparr>s24_second_post\<rparr> )" (is "_ \<ge> ?rhs")
      unfolding guar_inv_def using conj_seq_distrib guar_distrib_seq 
        rely_seq_idem conj.sync_mono_right by (metis (no_types, lifting))
    also have "?rhs \<ge> ( guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr> ) ; 
          Vt::= e\<^sub>t" 
      using post_assignment simp_to_post seq_mono_right by auto
    finally show ?thesis using seq_mono_right by (simp add: seq_assoc)
  qed
  also have step_25 : "?rhs \<ge> Vet ::= Constant N ; Vot ::= Constant N ; 
        ( ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> ) \<parallel>
          ( guar(ot_decreq \<inter> P' p_inv) \<iinter> rely(et_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>q2_25\<rparr> ) ) ;
        Vt::= e\<^sub>t" (is "_ \<ge> ?rhs")
  proof -
    have "rely no_change \<iinter> \<lparr>s24_first_post\<rparr> \<ge> rely no_change \<iinter> \<lparr>q1_25 \<inter> q2_25\<rparr>"
           (is "_ \<ge> ?rhs")
      using subset_8 conj.sync_mono_right spec_strengthen by auto
    also have "?rhs \<ge> (guar(no_change \<union> (et_decreq \<inter> P' p_inv)) \<iinter> 
          rely(no_change \<union> (ot_decreq \<inter> P' p_inv)) \<iinter> \<lparr>q1_25\<rparr>) \<parallel>
          (guar(no_change \<union> (ot_decreq \<inter> P' p_inv)) \<iinter> 
           rely(no_change \<union> (et_decreq \<inter> P' p_inv)) \<iinter> \<lparr>q2_25\<rparr>)" (is "_ \<ge> ?rhs")
      using spec_introduce_par by blast
    also have "?rhs = (guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lparr>q1_25\<rparr>) \<parallel>
          (guar(ot_decreq \<inter> P' p_inv) \<iinter> rely(et_decreq \<inter> P' p_inv) \<iinter> \<lparr>q2_25\<rparr>)" 
      using equality_2 equality_3 by auto
    finally have "rely no_change \<iinter> \<lparr>s24_first_post\<rparr> \<ge> 
          ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( guar(ot_decreq \<inter> P' p_inv) \<iinter> rely(et_decreq \<inter> P' p_inv) \<iinter> \<lparr>q2_25\<rparr>)"
             (is "_ \<ge> ?rhs")
      by simp
    then have "guar_inv p_inv \<iinter> rely no_change \<iinter> \<lparr>s24_first_post\<rparr> \<ge> 
          guar_inv p_inv \<iinter> 
          ( ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
            ( guar(ot_decreq \<inter> P' p_inv) \<iinter> rely(et_decreq \<inter> P' p_inv) \<iinter> \<lparr>q2_25\<rparr>) )"
             (is "_ \<ge> ?rhs")
      using conj.sync_mono_right conj_assoc by auto
    also have "?rhs \<ge> ( guar_inv p_inv \<iinter> guar(et_decreq \<inter> P' p_inv) \<iinter> 
          rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( guar_inv p_inv \<iinter> guar(ot_decreq \<inter> P' p_inv) \<iinter> 
            rely(et_decreq \<inter> P' p_inv) \<iinter> \<lparr>q2_25\<rparr>)" (is "_ \<ge> ?rhs")
      unfolding guar_inv_def using guar_distrib_par conj_assoc by auto
    also have "?rhs \<ge> ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( guar(ot_decreq \<inter> P' p_inv) \<iinter> rely(et_decreq \<inter> P' p_inv) \<iinter> \<lparr>q2_25\<rparr>)"
      using refinement_1 refinement_2 conj.sync_mono_left par.sync_mono by presburger
    finally have no_pre : "guar_inv p_inv \<iinter> rely no_change \<iinter> \<lparr>s24_first_post\<rparr> \<ge> 
          ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( guar(ot_decreq \<inter> P' p_inv) \<iinter> rely(et_decreq \<inter> P' p_inv) \<iinter> \<lparr>q2_25\<rparr>)" by auto
    then have "guar_inv p_inv \<iinter> rely no_change \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr> = 
          \<lbrace>p_inv\<rbrace>;( guar_inv p_inv \<iinter> rely no_change \<iinter> \<lparr>s24_first_post\<rparr>)" 
      using conj.sync_commute initial_assert_rely_generic by auto
    also have "\<dots> \<ge> ( guar(et_decreq \<inter> P' p_inv) \<iinter> rely(ot_decreq \<inter> P' p_inv) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr>) \<parallel> 
          (guar(ot_decreq \<inter> P' p_inv) \<iinter> rely(et_decreq \<inter> P' p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>q2_25\<rparr>)" 
      using no_pre seq_mono_right pre_par_distrib move_pre par.sync_mono by auto
    finally show ?thesis using seq_mono_right seq_mono_left by auto
  qed
  also have even_odd_refinement : "?rhs \<ge> Vet ::= Constant N ; Vot ::= Constant N ; 
  ((Vec::= Constant 0 ; While b\<^sub>w do If b\<^sub>i then Vet::= e\<^sub>1 else Vec::= e\<^sub>2 fi od) \<parallel>
   (Voc::= Constant 1 ; While b\<^sub>w\<^sub>o do If b\<^sub>i\<^sub>o then Vot::= e\<^sub>1\<^sub>o else Voc::= e\<^sub>2\<^sub>o fi od));
  Vt::= e\<^sub>t"
    using even_refinement odd_refinement par.sync_mono seq_mono_left seq_mono_right by auto
  finally show ?thesis .
qed
end
end