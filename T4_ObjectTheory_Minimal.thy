theory T4_ObjectTheory_Minimal
  imports Main
begin

text\<open>We construct a representation of Aczel-models which are a core ingredient of
     more complex models of object theory.\<close>

typedecl \<omega> \<comment> \<open>Type of Ordinary Urelements\<close>

typedecl \<sigma> \<comment> \<open>Type of Special Urelements\<close>

datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma> \<comment> \<open>Type of Urelements: Either Ordinary or Special\<close>

type_synonym \<Pi> = "\<upsilon> \<Rightarrow> bool" \<comment> \<open>Unary Relations among / "Properties of Urelements"\<close>

type_synonym \<alpha> = "\<Pi> set" \<comment> \<open>Type for Abstract Objects\<close>

datatype \<nu> = \<omega>\<nu> \<omega> | \<alpha>\<nu> \<alpha> \<comment> \<open>Individuals: Either Ordinary or Abstract\<close>

consts \<alpha>\<sigma> :: "\<alpha> \<Rightarrow> \<sigma>" \<comment> \<open>Mapping Abstract Objects to Special Urelements\<close>

primrec \<nu>\<upsilon> :: "\<nu> \<Rightarrow> \<upsilon>" where \<comment> \<open>Mapping Individuals to Urelements\<close>
  "\<nu>\<upsilon> (\<omega>\<nu> x) = \<omega>\<upsilon> x"
| "\<nu>\<upsilon> (\<alpha>\<nu> x) = \<sigma>\<upsilon> (\<alpha>\<sigma> x)"

text\<open>An individual exemplifies a property, if it maps its urelement to True.\<close>
definition Exe :: "\<Pi> \<Rightarrow> \<nu> \<Rightarrow> bool" ("\<lparr>_,_\<rparr>") where
  "\<lparr>F, x\<rparr> = F (\<nu>\<upsilon> x)"

text\<open>Encoding for Abstract Objects is determined by elementhood in the representation set.\<close>
primrec Enc :: "\<nu> \<Rightarrow> \<Pi> \<Rightarrow> bool" ("\<lbrace>_,_\<rbrace>") where
  "\<lbrace>\<alpha>\<nu> x,F\<rbrace> = (F \<in> x)"
| "\<lbrace>\<omega>\<nu> x,F\<rbrace> = False"

text\<open>For any condition \<phi> on properties, there is an (abstract) object that encodes
     exactly those properties that satisfy the condition.\<close>
lemma A_objects: "\<exists> x . \<forall>F . \<lbrace>x,F\<rbrace> \<longleftrightarrow> \<phi> F"
  (* sledgehammer *)
  by (metis Enc.simps(1) mem_Collect_eq)

text\<open>For any condition \<phi> on urelements, there is a property that is exemplified by
     exactly those objects, s.t. their urelement satisfies \<phi>.\<close>
lemma RelationComprehension: "\<exists>F . \<forall> x . \<lparr>F, x\<rparr> \<longleftrightarrow> \<phi> (\<nu>\<upsilon> x)"
  (* sledgehammer *)
  using Exe_def by auto

end