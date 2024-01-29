theory Our_RG_Syntax
imports 
"HOL-Hoare_Parallel.RG_Tran"  

begin

text \<open>Quote Antiquote code syntax is introduced from Quote_Antiquote theory with notation edit\<close>
syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)
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
  "\<ordmasculine>x" \<rightleftharpoons> "x \<acute>CONST fst"
  "\<ordfeminine>x" \<rightleftharpoons> "x \<acute>CONST snd"

abbreviation Skip :: "'a com"  ("SKIP")
  where "SKIP \<equiv> Basic id"

notation Seq  ("(_;;/ _)" [60,61] 60)

syntax
  "_Assign"    :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"                     ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_Cond"      :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a com"   ("(0IF _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)
  "_Cond2"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             ("(0IF _ THEN _ FI)" [0,0] 56)
  "_While"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             ("(0WHILE _ /DO _ /OD)"  [0, 0] 61)
  "_Await"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             ("(0AWAIT _ /THEN /_ /END)"  [0,0] 61)
  "_Atom"      :: "'a com \<Rightarrow> 'a com"                        ("(\<langle>_\<rangle>)" 61)
  "_Wait"      :: "'a bexp \<Rightarrow> 'a com"                       ("(0WAIT _ END)" 61)

translations
  "\<acute>x := a" \<rightharpoonup> "CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST Cond \<llangle>b\<rrangle> c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE SKIP FI"
  "WHILE b DO c OD" \<rightharpoonup> "CONST While \<llangle>b\<rrangle> c"
  "AWAIT b THEN c END" \<rightleftharpoons> "CONST Await \<llangle>b\<rrangle> c"
  "\<langle>c\<rangle>" \<rightleftharpoons> "AWAIT CONST True THEN c END"
  "WAIT b END" \<rightleftharpoons> "AWAIT b THEN SKIP END"


nonterminal prgs

syntax
  "_PAR"        :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" 60)
  "_prg"        :: "'a \<Rightarrow> prgs"              ("_" 57)
  "_prgs"       :: "['a, prgs] \<Rightarrow> prgs"      ("_//\<parallel>//_" [60,57] 57)

translations
  "_prg a" \<rightharpoonup> "[a]"
  "_prgs a ps" \<rightharpoonup> "a # ps"
  "_PAR ps" \<rightharpoonup> "ps"

syntax
  "_prg_scheme" :: "['a, 'a, 'a, 'a] \<Rightarrow> prgs"  ("SCHEME [_ \<le> _ < _] _" [0,0,0,60] 57)

translations
  "_prg_scheme j i k c" \<rightleftharpoons> "(CONST map (\<lambda>i. c) [j..<k])"

print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' \<^syntax_const>\<open>_antiquote\<close> t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const \<^syntax_const>\<open>_Assert\<close>);

    fun bexp_tr' name ((Const (\<^const_syntax>\<open>Collect\<close>, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const \<^syntax_const>\<open>_Assign\<close> $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;
  in
   [(\<^const_syntax>\<open>Collect\<close>, K assert_tr'),
    (\<^const_syntax>\<open>Basic\<close>, K assign_tr'),
    (\<^const_syntax>\<open>Cond\<close>, K (bexp_tr' \<^syntax_const>\<open>_Cond\<close>)),
    (\<^const_syntax>\<open>While\<close>, K (bexp_tr' \<^syntax_const>\<open>_While\<close>))]
  end
\<close>

end