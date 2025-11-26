(* This is  comment. *)
theory T1_Isabelle_Pure (* The Theory name must exactly match the file name (without .thy) *)
  imports Main (* The standard base theory for Isabelle/HOL is called Main *)
begin

text\<open>
  \<^item> Isabelle is a generic proof assistant; a framework for automated and interactive reasoning
    and theorem proving relative to various logical systems.
  \<^item> It stands in the tradition of the LCF theorem prover with a trusted reasoning
    core implemented in Standard ML @{url \<open>https://doi.org/10.1007%2F3-540-09724-4\<close>}.
  \<^item> It implements various Object Logics (e.g. Isabelle/FOL, Isabelle/ZF, etc.);
    We look in particular at Isabelle/HOL.
\<close>

(* Outer Syntax                                  *)
(* <------------------------------------------>  *)
(*          Inner Syntax (Quoted)                *)
(*          <--------------------------------->  *)
(*          Pure Logic (Metalogic)               *)
(*           <------------------------------->   *)
(*           Object Logic: HOL                   *)
(*           <--------------->     <->     <->   *)
   lemma L: "\<forall> x . P x \<longrightarrow> Q x \<Longrightarrow> P x \<Longrightarrow> Q x"
(* Outer Syntax (proof) *)
(*   <----->            *)
     by auto

thm L (* Show me the statement of lemma L.
        The question mark in the output at the bottom indicates that the lemma is true for
        arbitrary variables.*)
thm L[of A B y] (* Instantiate the theorem to different variables.*)

section\<open>Markup for verified documents.\<close>

text\<open>Text to be output in a generated verified document.
     Remark: Text can refer to inner syntax terms @{term \<open>\<forall> x . P x \<longrightarrow> Q x\<close>},
     outer syntax commands @{command lemma}, theorems @{thm L},
     etc. (via "antiquotations" like @{term x}).\<close>

section\<open>Isabelle/Pure\<close>

subsection\<open>Pure Logic and Propositions\<close>

text\<open>Meta-implication "from A it follows that B"\<close>
prop "A \<Longrightarrow> B"

text\<open>Meta-equivalence or "Pure equality" - mainly used in definitions later\<close>
prop "A \<equiv> B"

text\<open>Meta-conjunction - rarely used explicitly\<close>
prop "A &&& B"

text\<open>Meta-quantifier - "for all x it holds that P x"\<close>
prop "\<And> x . P x"

subsection\<open>Types and Terms\<close>

typedecl i \<comment> \<open>Declare an uninterpreted type @{typ i}. It's axiomatically inhabited
              (there is an object of type @{typ i}).\<close>

text \<open>Terms can be typed.\<close>
term "x :: i"

text \<open>Functions of types are types.\<close>
term "y :: i \<Rightarrow> i"

typ "prop" \<comment> \<open>Basic type of Isabelle/Pure propositions. Rarely used explicitly.\<close>

text\<open>Function application.\<close>
prop "P x"

text\<open>Functions get function types; types are inferred.\<close>
prop "(P::i\<Rightarrow>bool) (x::i)" \<comment> \<open>Note: we're actually already in HOL here with bool as type of propositions\<close>

text\<open>Polymorphic Types: referring to arbitrary types\<close>
prop "(P::'a\<Rightarrow>'b) (x::'a) \<equiv> (y::'b)"

text\<open>Note: We rarely need to care about the Isabelle/Pure meta-logic itself,
           but mainly work in the object-logic HOL.\<close>

end
