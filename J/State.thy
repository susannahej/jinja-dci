(*  Title:      Jinja/J/State.thy

    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)
(*
  Expanded to include support for static fields and methods.
  Susannah Mansky
  2017, UIUC
*)

section \<open> Program State \<close>

theory State imports "../Common/Exceptions" begin

type_synonym
  locals = "vname \<rightharpoonup> val"      \<comment> \<open>local vars, incl. params and ``this''\<close>
type_synonym
  state  = "heap \<times> locals \<times> sheap"

definition hp :: "state \<Rightarrow> heap"
where
  "hp  \<equiv>  fst"
definition lcl :: "state \<Rightarrow> locals"
where
  "lcl  \<equiv>  fst \<circ> snd"
definition shp :: "state \<Rightarrow> sheap"
where
  "shp  \<equiv>  snd \<circ> snd"

(*<*)
declare hp_def[simp] lcl_def[simp] shp_def[simp]
(*>*)

end
