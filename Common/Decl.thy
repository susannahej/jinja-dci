(*  Title:      JinjaDCI/Common/Decl.thy

    Author:     David von Oheimb, Susannah Mansky
    Copyright   1999 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory Common/Decl.thy by David von Oheimb
*)

section \<open> Class Declarations and Programs \<close>

theory Decl imports Type begin

type_synonym 
  fdecl    = "vname \<times> staticb \<times> ty"        \<comment> \<open>field declaration\<close>
type_synonym
  'm mdecl = "mname \<times> staticb \<times> ty list \<times> ty \<times> 'm"     \<comment> \<open>method = name, static flag, arg.\ types, return type, body\<close>
type_synonym
  'm "class" = "cname \<times> fdecl list \<times> 'm mdecl list"       \<comment> \<open>class = superclass, fields, methods\<close>
type_synonym
  'm cdecl = "cname \<times> 'm class"  \<comment> \<open>class declaration\<close>
type_synonym
  'm prog  = "'m cdecl list"     \<comment> \<open>program\<close>

(* replaced all fname, mname, cname in below with `char list' so that
 pretty printing works   -SM *)
(*<*)
translations
  (type) "fdecl"   <= (type) "char list \<times> staticb \<times> ty"
  (type) "'c mdecl" <= (type) "char list \<times> staticb \<times> ty list \<times> ty \<times> 'c"
  (type) "'c class" <= (type) "char list \<times> fdecl list \<times> ('c mdecl) list"
  (type) "'c cdecl" <= (type) "char list \<times> ('c class)"
  (type) "'c prog" <= (type) "('c cdecl) list"
(*>*)

definition "class" :: "'m prog \<Rightarrow> cname \<rightharpoonup> 'm class"
where
  "class  \<equiv>  map_of"

(* Not difficult to prove, but useful for directing particular sequences of equality -SM *)
lemma class_cons: "\<lbrakk> C \<noteq> fst x \<rbrakk> \<Longrightarrow> class (x # P) C = class P C"
 by (simp add: class_def)

definition is_class :: "'m prog \<Rightarrow> cname \<Rightarrow> bool"
where
  "is_class P C  \<equiv>  class P C \<noteq> None"

lemma finite_is_class: "finite {C. is_class P C}"
(*<*)
apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done
(*>*)

definition is_type :: "'m prog \<Rightarrow> ty \<Rightarrow> bool"
where
  "is_type P T  \<equiv>
  (case T of Void \<Rightarrow> True | Boolean \<Rightarrow> True | Integer \<Rightarrow> True | NT \<Rightarrow> True
   | Class C \<Rightarrow> is_class P C)"

lemma is_type_simps [simp]:
  "is_type P Void \<and> is_type P Boolean \<and> is_type P Integer \<and>
  is_type P NT \<and> is_type P (Class C) = is_class P C"
(*<*)by(simp add:is_type_def)(*>*)


abbreviation
  "types P == Collect (is_type P)"

lemma class_exists_equiv:
 "(\<exists>x. fst x = cn \<and> x \<in> set P) = (class P cn \<noteq> None)"
apply (rule iffI)
\<comment> \<open> @{text \<Rightarrow>} \<close>
apply (simp, simp only: class_def)
using weak_map_of_SomeI apply fastforce
\<comment> \<open> @{text \<Leftarrow>} \<close>
apply (simp add: class_def)
apply (meson map_of_SomeD)
done

lemma class_exists_equiv2:
 "(\<exists>x. fst x = cn \<and> x \<in> set (P1 @ P2)) = (class P1 cn \<noteq> None \<or> class P2 cn \<noteq> None)"
by (simp only: class_exists_equiv [where P = "P1@P2"], simp add: class_def)

end
