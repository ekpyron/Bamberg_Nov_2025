(* This is  comment. *)
theory T2_Isabelle_HOL (* The Theory name must exactly match the file name (without .thy) *)
  imports Main (* The standard base theory for Isabelle/HOL is called Main *)
begin

section\<open>Isabelle/HOL\<close>

text\<open>Isabelle/HOL provides classical higher-order logic as object logic
     on top of Isabelle/Pure and is part of the base @{theory Main}.\<close>

text\<open>The type of HOL propositions is @{typ bool}.\<close>
prop "x::bool"

text\<open>@{term True} and @{term False} are truth and falsity in type @{typ bool}.\<close>
term True
term False

text\<open>We get classical (extensional) logical connectives
     adhering to classical logical rules - for example:\<close>

lemma "(p \<and> q) = (\<not>(p \<longrightarrow> \<not>q))"
  try \<comment> \<open>Try to automatically find a proof. Insert by clicking it.
         We often also use "try0" for trivial proofs (without the need of other facts);
         "sledgehammer" for complex proofs (that may need to refer to other facts) or
         "nitpick" to find counterexamples.}\<close>
  try0 \<comment> \<open>Various methods can prove our lemma directly.\<close>
  nitpick \<comment> \<open>There are no counterexamples.\<close>
  sledgehammer \<comment> \<open>sledgehammer is slower, but can also find more complex proofs\<close>
  by auto \<comment> \<open>We can choose any of the suggested proofs to prove our lemma.\<close>
lemma "(p \<or> q) = (\<not>p \<longrightarrow> q)"
  by auto
lemma "(p \<longleftrightarrow> q) = ((p \<longrightarrow> q) \<and> (q \<longrightarrow> p))"
  by auto
lemma "(\<exists> x . F x) = (\<not>(\<forall> x . \<not>F x))"
  by auto
lemma \<open>(\<forall> x . F x) \<longrightarrow> F y\<close> \<comment> \<open>Not a free logic as object theory!\<close>
  by auto

lemma "p \<and> q \<longrightarrow> p"
  by auto
lemma "p \<and> q \<longrightarrow> q"
  by auto
lemma "p \<longrightarrow> q \<longrightarrow> p \<and> q"
  by auto

lemma "(\<not>p) = (p \<longrightarrow> False)"
  by auto
lemma "\<not>(p \<and> \<not>p)"
  by auto
lemma "p \<or> \<not>p"
  by auto
lemma "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r) \<longrightarrow> (p \<or> q \<longrightarrow> r)"
  by auto

lemma "True \<noteq> False"
  by auto
lemma "p = True \<or> p = False"
  by auto

lemma "(\<forall>x . f x = g x) \<longleftrightarrow> f = g"
  by auto


subsection\<open>Typing (entering) Symbols in Isabelle\<close>

text\<open>Isabelle allows the use of common syntax for logical symbols. They can be
     selected manual using the "Symbols" tab at the bottom of the window.
     More conveniently, they can be entered by using a backslash "\" followed by
     latex-style names for symbols.\<close>

text\<open>For example:
     \<forall> can by typed using \forall which will open a context menu for selecting a matching symbol.
     One they context menu appears use "Tab" to accept the first suggestion.\<close>

text\<open>Common logical connectives have even more convenient shortcuts, e.g.
     \<and> can simply be typed as /\, \<or> as \/, \<longrightarrow> as -->

     Note that such shortcuts will only be immediately replaced in "inner syntax" context, i.e.
     within quotation marks:\<close>
term "x \<and> y \<longrightarrow> z"
term "\<forall> F . F x \<longrightarrow> F x" \<comment> \<open>Green print suggests an identifier is *bound*.\<close>
term "(\<forall>x . F x) \<longrightarrow> F x" \<comment> \<open>Note: the last x is outside the scope of the quantifier; not bound by it.\<close>

subsection\<open>Constants, Axioms\<close>

text\<open>We introduce a constant of type @{typ bool}.\<close>
consts c :: bool

text\<open>A boolean constant must either be True or False\<close>
lemma "c = True \<or> c = False"
  by auto

text\<open>But we do not know whether it is True or False!\<close>
lemma "c"
  try \<comment> \<open>Reports a counterexample!\<close>
  nitpick[show_consts] \<comment> \<open>Shows a counterexample\<close>
  nitpick[satisfy, show_consts] \<comment> \<open>Shows a model (an interpretation in which the lemma is true)\<close>
  oops \<comment> \<open>We cannot prove the lemma, so abort the proof and forget we ever stated the lemma.\<close>

text\<open>We can introduce Axioms to shape the behaviour of constants.\<close>
axiomatization where c_is_not_false: "c \<noteq> False"

text\<open>Using the axiom we can prove that "c" holds:\<close>
lemma "c"
  using c_is_not_false by auto

text\<open>Careful! We can formulate inconsistent axioms! We can ask nitpick to confirm that
     there are models.\<close>
lemma "True"
  nitpick[satisfy, user_axioms, show_consts]  ..
  \<comment> \<open>"satisfy" asks nitpick to find a model instead of a countermodel
     "user_axioms" asks nitpick to consider our axioms
     "show_consts" asks nitpick to print the values it chose for relevant constants\<close>

text\<open>Commented example of an inconsistent axiomatization:\<close>

(*
axiomatization where c_is_false: \<open>\<not>c\<close>

lemma "True"
  nitpick[satisfy, user_axioms, show_consts] \<comment> \<open>Finds no model!\<close>
  oops
lemma "False"
  sledgehammer \<comment> \<open>Try to find a proof.\<close>
  using c_is_not_false c_is_false by blast

text\<open>Our new axiom is inconsistent with our previous one!\<close>
*)

text\<open>Often, axioms can be avoided by using purely definitional constructions, which can never
     end up inconsistent (we will see examples).\<close>

subsection\<open>Connection between HOL connectives with Pure connectives (using examples).\<close>

lemma "a \<longrightarrow> b \<Longrightarrow> a \<Longrightarrow> b"
  by auto
text\<open>Read the above as "if a implies b, then given a I can derive b".\<close>

lemma "(a \<Longrightarrow> b) \<Longrightarrow> a \<longrightarrow> b"
  by auto
text\<open>Read the above as "if under the assumption of a I can derive b, then a implies b".\<close>

lemma "\<forall>x . P x \<Longrightarrow> P y"
  by auto
text\<open>Read the above as "if I know that for all x, P x, then I can derive P y.\<close>

lemma "(\<And> x . P x) \<Longrightarrow> \<forall> x . P x"
  by auto
text\<open>Read the above as "if I can derive P x for an arbitrary x, it follows that for all x, P x.\<close>

subsection\<open>Extending the language with Definitions and Syntax\<close>

definition PropertyConjunction :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infix "\<oplus>" 100) where
  "PropertyConjunction F G \<equiv> \<lambda> y . F y \<and> G y"

lemma "F \<oplus> G = PropertyConjunction F G" \<comment> \<open>Demonstrate how the introduced syntax works.\<close>
  by auto

lemma "(F \<oplus> G) x \<longleftrightarrow> (F x \<and> G x)"
  sledgehammer
  by (simp add: PropertyConjunction_def)

lemma "(\<forall> x . Q x \<longrightarrow> (P \<oplus> R) x) \<Longrightarrow> (\<forall> x . R x \<longrightarrow> \<not>P x) \<Longrightarrow> \<forall> x . \<not>Q x"
  unfolding PropertyConjunction_def
  by auto

text\<open>HOL is higher-order and polymorphic!\<close>

lemma \<open>(\<lambda> x . x = x) (\<lambda> F G . F z \<longrightarrow> G z) \<and> (\<lambda>x . x = x) z\<close>
  by auto

subsection\<open>Church's Simple Theory of Types in HOL\<close>

text\<open>We will not dicuss this in detail, but for those familiar:
     The HOL logic is basically Church's Simple Theory of Types with Identity as well
     as definite and indefinite choice operators.\<close>

typedecl \<iota> \<comment> \<open>No fixed type of individuals, but we can declare arbitrary types.\<close>
type_synonym \<o> = bool \<comment> \<open>bool as type of propositions\<close>

subsubsection\<open>Base types\<close>
typ \<iota> \<comment> \<open>Individuals\<close>
typ \<o> \<comment> \<open>Propositions\<close>
typ "'a \<Rightarrow> 'b" \<comment> \<open>Functions\<close>

subsubsection\<open>Examples of types\<close>
typ "\<iota> \<Rightarrow> \<o>"
typ "(\<iota> \<Rightarrow> \<o>) \<Rightarrow> \<o>"
typ "((\<iota> \<Rightarrow> \<o>) \<Rightarrow> \<o>) \<Rightarrow> \<iota>"
typ "((\<iota> \<Rightarrow> \<o>) \<Rightarrow> \<o>) \<Rightarrow> (\<iota> \<Rightarrow> \<iota>)"

subsubsection\<open>Terms\<close>
term "x::'a"
term "(\<lambda>x :: 'a . \<phi> x::'b)::'a\<Rightarrow>'b"
term "THE x . \<phi> x" \<comment> \<open>Definite Choice Operator\<close>
term "(THE x ::'a . (\<phi>::'a\<Rightarrow>\<o>) x)::'a" \<comment> \<open>Definite Choice Operator (explicit types)\<close>

subsubsection\<open>Formulas\<close>
prop "p \<or> q" \<comment> \<open>Disjunction\<close>
prop "p \<longrightarrow> q" \<comment> \<open>Implication\<close>
prop "\<forall>x . \<phi> x" \<comment> \<open>Quantification\<close>
prop "\<forall>x :: 'a . (\<phi>::'a\<Rightarrow>\<o>) x" \<comment> \<open>Quantification (explicit types)\<close>
prop "F a" \<comment> \<open>Function application\<close>
prop "(F::'a\<Rightarrow>\<o>) (x::'a)" \<comment> \<open>Function application (explicit types)\<close>
prop "(\<lambda>x . F x \<or> G x) y" \<comment> \<open>Example of complex formula\<close>
prop "x = y" \<comment> \<open>Identity\<close>

subsubsection\<open>Axioms and Rules\<close>

text\<open>Modus Ponens\<close>
lemma ModusPonens: "A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B" using mp.

text\<open>\<alpha>-equivalence is builtin (internally formulas are represented with de-Bruijin indices)\<close>
lemma \<alpha>: "(\<lambda> x. \<phi> x) = (\<lambda>y . \<phi> y)"..

text\<open>\<beta>-conversion\<close>
lemma \<beta>: "(\<lambda> x . \<phi> x) y = \<phi> y"..

text\<open>\<eta>-contraction\<close>
lemma \<eta>: "(\<lambda> x . \<phi> x) = \<phi>"..

text\<open>Identity and Substitution\<close>
lemma "x = x" using refl.
lemma "(\<And> x . f x = g x) \<Longrightarrow> f = g" using ext.
lemma "x = y \<Longrightarrow> F x \<Longrightarrow> F y" using subst.

text\<open>Definite Choice\<close>
lemma "(THE x . x = a) = a" using the_eq_trivial.

text\<open>We also get indefinite choice\<close>
term "SOME x . \<phi> x"
lemma "P x \<Longrightarrow> P (SOME x . P x)" using someI.

text\<open>Note: Church's Simple Theory of Types requires several more Axioms.
           For the curious we show below that we have all of them in terms
           of a simpler axiomatization.\<close>

subsection\<open>System \<open>\<Q>\<^sub>0\<close>\<close>
text\<open>The actual construction of HOL is closer to Peter Andrew's \<open>\<Q>\<^sub>0\<close>.
     See @{url \<open>https://plato.stanford.edu/entries/type-theory-church/#FormBaseEqua\<close>}\<close>

term "(=)" \<comment> \<open>\<open>Q\<close>\<close>
lemma "(A = B) = (=) A B"..
lemma "(A \<longleftrightarrow> B) = (A = B)".. \<comment> \<open>\<open>\<equiv>\<close>\<close>
lemma "True = ((=) = (=))" \<comment> \<open>\<open>T\<^sub>0\<close>\<close>
  by auto
lemma "False = ((\<lambda> x . True) = (\<lambda> x . x))" \<comment> \<open>\<open>F\<^sub>0\<close>\<close>
  by metis
lemma "All = (=) (\<lambda> x . True)" \<comment> \<open>\<open>\<Pi>\<close>\<close>
  by auto
term All \<comment> \<open>\<Pi>\<close>
lemma "(\<forall>x . \<phi> x) = All \<phi>"..
lemma "(\<and>) = (\<lambda>x y . (\<lambda> g::\<o>\<Rightarrow>\<o>\<Rightarrow>\<o> . g True True) = (\<lambda>g . g x y))"
  by (metis (full_types))
lemma "(\<phi> \<and> \<psi>) = (\<and>) \<phi> \<psi>"..
lemma "Not = (=) False"
  by auto
lemma "(\<not>\<phi>) = Not \<phi>"..

lemma Q1: "(g True \<and> g False) = (\<forall>x . g x)"
  by (metis (full_types))
lemma Q2: "(x = y) \<longrightarrow> (f x = f y)"
  by auto
lemma Q3: "(f = g) = (\<forall> x . f x = g x)"
  by auto
lemma Q4: "(\<lambda> x . \<phi> x) y = \<phi> y"..
lemma Q5: "(THE x . x = y) = y" using the_eq_trivial.

text\<open>You can actually look at the precise construction of the HOL-logic itself!
     Use Ctrl-click on one the following theorem to jump to HOLs own construction
     in Isabelle/Pure. Note: this will not be easy to read without a good deal of
     familiarity with Isabelle/HOL.\<close>
thm refl

subsection\<open>Contents of @{theory Main}\<close>

text\<open>Note that @{theory Main} contains a lot more than we have seen and
     as we can show in our course, including natural numbers, lists, (typed) sets,
     mathematical theories like group theory, order theory,
     definite and indefinite choice operators, etc. pp.

     See also: "Isabelle reference Manuals/main" in the Documentation Tab
               on the left-hand-side of the Isabelle window.\<close>

subsection\<open>apply-style vs Isar-style (Intelligible semi-automated reasoning)\<close>

text\<open>There are multiple ways to construct proofs for lemmas/theorems:\<close>

text\<open>We can use automated methods to prove theorems:\<close>
lemma "\<forall>x . P x \<longrightarrow> P x \<or> Q x"
  by auto

text\<open>These methods perform multiple steps that transform the current goal:\<close>
lemma "\<forall>x . P x \<longrightarrow> P x \<or> Q x"
  apply (rule allI) \<comment> \<open>Introduction rule for the all-quantifier\<close>
  apply (rule impI) \<comment> \<open>Introduction rule for implication\<close>
  apply (rule disjI1) \<comment> \<open>Left-introduction for the disjunction\<close>
  . \<comment> \<open>Our goal is among our assumptions.\<close>

text\<open>We can also, more naturally, use structured proofs in the Isar language:\<close>
lemma "\<forall>x . P x \<longrightarrow> P x \<or> Q x"
proof \<comment> \<open>Start an Isar proof with a default introduction rule\<close>
  fix x \<comment> \<open>Choose an arbitrary x\<close>
  { \<comment> \<open>Start a sub-proof to prove the implication.\<close>
    assume "P x" \<comment> \<open>Assume the antecedant.\<close>
    then have "P x \<or> Q x" \<comment> \<open>Derive the consequent by disjunction introduction.\<close>
      by (rule disjI1) \<comment> \<open>Could also use automated methods, e.g. "by auto", or sledgehammer\<close>
  } \<comment> \<open>our block shows that @{prop \<open>P x \<Longrightarrow> P x \<or> Q x\<close>}\<close>
  then show "P x \<longrightarrow> P x \<or> Q x" \<comment> \<open>Our goal follows by implication introduction.\<close>
    by (rule impI)
qed \<comment> \<open>We have concluded the proof\<close>

text\<open>See also e.g. the "src/HOL/Examples/Drinker.thy" example in the Examples section in the
     Documentation tab on the left-hand side of the Isabelle window.\<close>

end
