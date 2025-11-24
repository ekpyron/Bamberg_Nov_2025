theory T3_Datatypes_and_Functions
  imports Main
begin

section\<open>Datatypes\<close>

text\<open>Isabelle allows to introduce "datatypes" using one or more "constructors".\<close>

datatype Color = Red | Green | Blue

typ Color \<comment> \<open>Color is a type\<close>

text\<open>Red, Green and Blue are terms of type Color\<close>
term Red
term Blue
term Green

term "x::Color" \<comment> \<open>We can use variables of type Color. Note that Isabelle can most of the time
                   infer the proper types from context.\<close>

text\<open>An object of type Color is either Red, Blue or Green\<close>
lemma \<open>x = Red \<or> x = Blue \<or> x = Green\<close>
  (* sledgehammer *)
  using Color.exhaust by blast
text\<open>We *can* type everything, but usually don't have to.\<close>
lemma \<open>(x::Color) = (Red::Color) \<or> (x::Color) = (Blue::Color) \<or> (x::Color) = (Green::Color)\<close>
  using Color.exhaust by blast

text\<open>All colors are distinct.\<close>
lemma \<open>Red \<noteq> Blue \<and> Red \<noteq> Green \<and> Blue \<noteq> Green\<close>
  by auto

subsection\<open>Primitive recursive functions.\<close>

primrec is_blue_or_green :: \<open>Color \<Rightarrow> bool\<close> where
  "is_blue_or_green Red = False"
| "is_blue_or_green Green = True"
| "is_blue_or_green Blue = True"

lemma "x \<noteq> Red \<longrightarrow> is_blue_or_green x"
  sledgehammer
  by (metis Color.exhaust is_blue_or_green.simps(2,3))

subsection\<open>Recursive Datatypes\<close>

text\<open>We can define datatypes based on other datatypes and using recursion:\<close>

datatype ComplexColor = BaseColor Color | MixOfColors ComplexColor ComplexColor

term BaseColor \<comment> \<open>BaseColor takes a Color and produces a ComplexColor\<close>
term MixOfColors \<comment> \<open>MixOfColors takes two Colors and produces a ComplexColor\<close>
term "BaseColor Red" \<comment> \<open>"BaseColor Red" is a ComplexColor\<close>
term "MixOfColors (BaseColor Red) (BaseColor Green)" \<comment> \<open>The mix of BaseColors Red and Green is a ComplexColor\<close>

definition Yellow :: ComplexColor where
  "Yellow \<equiv> MixOfColors (BaseColor Red) (BaseColor Green)"
definition Magenta :: ComplexColor where
  "Magenta \<equiv> MixOfColors (BaseColor Red) (BaseColor Blue)"
definition Cyan :: ComplexColor where
  "Cyan \<equiv> MixOfColors (BaseColor Green) (BaseColor Blue)"

lemma "Yellow \<noteq> Magenta"
  by (simp add: Magenta_def Yellow_def)

primrec contains_basecolor :: "ComplexColor \<Rightarrow> Color \<Rightarrow> bool" where
  "contains_basecolor (BaseColor x) y = (x = y)"
| "contains_basecolor (MixOfColors x y) z = (contains_basecolor x z \<or> contains_basecolor y z)"

lemma "contains_basecolor Yellow Red \<and> contains_basecolor Yellow Green \<and> \<not>contains_basecolor Yellow Blue"
  by (simp add: Yellow_def)

lemma "contains_basecolor x Red \<or> contains_basecolor x Green \<or> contains_basecolor x Blue"
  \<comment> \<open>sledgehammer - automatic proving quickly fails on nested structures\<close>
  apply (induct x) \<comment> \<open>We can prove inductively by cases\<close>
   apply (metis Color.exhaust contains_basecolor.simps(1))
  apply simp
  by auto

text\<open>Note that this is a silly example:\<close>
lemma "BaseColor Blue \<noteq> MixOfColors (BaseColor Blue) (BaseColor Blue)"
  by simp
lemma "MixOfColors (BaseColor Blue) (BaseColor Red) \<noteq> MixOfColors (BaseColor Red) (BaseColor Blue)"
  by simp

primrec is_base_color :: "ComplexColor \<Rightarrow> bool" where
  "is_base_color (BaseColor x) = True"
| "is_base_color (MixOfColors x y) = (is_base_color x \<and> is_base_color y \<and> x = y)"

lemma "is_base_color (BaseColor x)"
  by simp
lemma "is_base_color (MixOfColors (BaseColor Blue) (BaseColor Blue))"
  by simp
lemma "\<not>is_base_color Yellow"
  by (simp add: Yellow_def)

section\<open>Isabelle/HOL gives us builtin types like flat sets or natural numbers\<close>

primrec set_of_base_colors :: "ComplexColor \<Rightarrow> Color set" where
  "set_of_base_colors (BaseColor x) = {x}"
| "set_of_base_colors (MixOfColors x y) = set_of_base_colors x \<union> set_of_base_colors y"

value "set_of_base_colors Yellow"
lemma "set_of_base_colors Yellow = {Red, Green}"
  by (metis Un_empty_right Yellow_def insert_def set_of_base_colors.simps(1,2))
lemma "set_of_base_colors Yellow = {Green, Red}"
  by (metis Un_insert_right Yellow_def insert_is_Un set_of_base_colors.simps(1,2))
lemma "Blue \<notin> set_of_base_colors Yellow"
  by (simp add: Yellow_def)

lemma L1: "is_base_color x \<Longrightarrow> \<exists> y . set_of_base_colors x = {y}"
  apply (induct x)
  apply simp
  by simp

lemma L2: "contains_basecolor x y \<Longrightarrow> y \<in> set_of_base_colors x"
  apply (induct x)
  apply simp
  by fastforce

text\<open>Example of sledgehammer finding a proof based on previous proofs.\<close>
lemma "is_base_color x \<Longrightarrow> contains_basecolor x y \<Longrightarrow> set_of_base_colors x = {y}"
  (* sledgehammer *)
  using L1 L2 by fastforce

lemma "set_of_base_colors (MixOfColors x y) = set_of_base_colors (MixOfColors y x)"
  by auto

text\<open>
To quote Tobias Nipkow:
  HOL = Functional Programming + Logic
  (see "Isabelle Tutorials/prog-prove" in the "Documentation" tab on the left of Isabelle)
\<close>

end