theory Predicates
  imports
    "../General/Relations"
    "../Programming/State_Relations"
    "../Programming/Expressions"
begin

text \<open>Quote Antiquote code syntax is introduced from Quote_Antiquote theory with notation edit\<close>
syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<Zprime>_" [1000] 1000)
  "_Assert"    :: "'a \<Rightarrow> 'a set"                    ("(\<llangle>_\<rrangle>)" [0] 1000)

translations
  "\<llangle>b\<rrangle>" \<rightharpoonup> "CONST Collect \<guillemotleft>b\<guillemotright>"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr \<^syntax_const>\<open>_antiquote\<close> t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(\<^syntax_const>\<open>_quote\<close>, K quote_tr)] end
\<close>

text \<open>More code from RG_Syntax\<close>
syntax
  "_before" :: "id \<Rightarrow> 'a" ("\<ordmasculine>_")
  "_after"  :: "id \<Rightarrow> 'a" ("\<ordfeminine>_")

translations
  "\<ordmasculine>x" \<rightleftharpoons> "x \<Zprime>CONST fst"
  "\<ordfeminine>x" \<rightleftharpoons> "x \<Zprime>CONST snd"
value "Id_on"


text \<open>We use (\<lpred>p\<rpred>) to give a relation where (\<sigma>,\<sigma>') satisfy predicate p\<close>


definition relation :: "(('state*'state) \<Rightarrow> bool) \<Rightarrow> 'state rel" ("\<lpred>_\<rpred>" [30])
  where "relation r \<equiv> Collect(r)"

definition predset :: "('state \<Rightarrow> bool) \<Rightarrow> 'state set" ("\<lrel>_\<rrel>" [30])
  where "predset p \<equiv> Collect(p)"

definition relseq :: "(('state*'state) \<Rightarrow> bool) \<Rightarrow> (('state*'state) \<Rightarrow> bool) \<Rightarrow> (('state*'state) \<Rightarrow> bool)" (infixr "\<Zcomp>" 30)
  where "relseq q r \<equiv> \<lambda> (s, s''). (\<exists>s'. q (s, s') \<and> r (s', s''))"

definition lambda_and :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "|\<and>|" 30)
  where "lambda_and p q \<equiv> (\<lambda>s. p s \<and> q s)"

definition lambda_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "|\<or>|" 30) 
  where "lambda_or p q \<equiv> (\<lambda>s. p s \<or> q s)"

definition lambda_and_big :: "('a \<Rightarrow> bool) set \<Rightarrow> ('a \<Rightarrow> bool)" ("|\<And>|_" 30)
  where "lambda_and_big ps \<equiv> (\<lambda>s. (\<forall>p\<in>ps. p s))"

definition lambda_or_big :: "('a \<Rightarrow> bool) set \<Rightarrow> ('a \<Rightarrow> bool)" ("|\<Or>|_" 30)
  where "lambda_or_big ps \<equiv> (\<lambda>s. (\<exists>p\<in>ps. p s))"

context state_relations
begin
definition id_rel :: "('state*'state) \<Rightarrow> bool" where
"id_rel s \<equiv> \<forall>x. ((get_var x (fst s)) = (get_var x (snd s)))"


(*TODO - Need to make work with RG_Hoare syntax*)
definition id_rel_bar :: "'varname fset \<Rightarrow> bool" where
"id_rel_bar xs \<equiv> \<llangle>\<forall>x. x|\<notin>|xs \<longrightarrow> (\<ordfeminine>x = \<ordmasculine>x)\<rrangle>"

definition id_bar_sing :: "'varname \<Rightarrow> ('state*'state) \<Rightarrow> bool" ("id\<^sub>__" [30, 30]) where
"id_bar_sing x s \<equiv> id_rel_bar {|x|} s"

lemma "\<lpred>id_rel\<rpred> \<subseteq> id_bar xs"
  by (smt (verit, ccfv_SIG) fst_conv id_rel_def mem_Collect_eq relation_def snd_conv split_conv state_relations.id_bar_def state_relations_axioms subrelI)

lemma "\<lpred>id_rel\<rpred> = id_bar fempty"
  by (smt (verit, ccfv_SIG) Collect_cong UNIV_I ex_fin_conv id_bar_def id_rel_def prod.collapse relation_def split_def)

lemma "\<lpred>id_rel_bar xs\<rpred> = id_bar xs"
  by (smt (verit, del_insts) Collect_cong UNIV_I case_prod_unfold fst_conv id_bar_def id_rel_bar_def relation_def snd_conv)
end


lemma rel_eq: "(\<lpred>q1\<rpred> \<subseteq> \<lpred>q2\<rpred>) = (\<forall> s. q1 s \<longrightarrow> q2 s)"
proof -
  have "\<lpred>q1\<rpred> \<subseteq> \<lpred>q2\<rpred> \<Longrightarrow> (\<forall> x. q1 x \<longrightarrow> q2 x)" by (metis (mono_tags, lifting) Collect_mono_iff UNIV_I prod.collapse relation_def split_def)
  also have "(\<forall> x. q1 x \<longrightarrow> q2 x) \<Longrightarrow> \<lpred>q1\<rpred> \<subseteq> \<lpred>q2\<rpred>" using relation_def by auto
  thus ?thesis using calculation by blast
  qed

lemma pred_eq: "(\<lrel>p1\<rrel> \<subseteq> \<lrel>p2\<rrel>) = (\<forall>s. p1 s \<longrightarrow> p2 s)"
  by (simp add: Collect_mono_iff predset_def)

lemma dom_restrict: "(\<lrel>p\<rrel> \<triangleleft> \<lpred>q2\<rpred> \<subseteq> \<lpred>q1\<rpred>) = (\<forall>s. p (fst s) \<and> q2 s \<longrightarrow> q1 s)"
  by (simp add: Collect_mono_iff Int_def predset_def relation_def restrict_domain_def)

lemma range_restrict: "(\<lpred>q2\<rpred> \<triangleright> \<lrel>p\<rrel> \<subseteq> \<lpred>q1\<rpred>) = (\<forall>s. p (snd s) \<and> q2 s \<longrightarrow> q1 s)"
  by (smt (verit) Int_iff UNIV_def mem_Collect_eq predset_def prod.collapse relation_def restrict_range_def split_def subset_iff)


lemma "(Range (\<lrel>p\<rrel> \<triangleleft> \<lpred>r\<rpred>)) \<subseteq> (\<lpred>r\<rpred> `` \<lrel>p\<rrel>)"
  using restrict_domain_def by fastforce

lemma relseqeq: "\<lpred>q \<Zcomp> r\<rpred> = \<lpred>q\<rpred> O \<lpred>r\<rpred>"
  sorry

end