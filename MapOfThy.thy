(*  Title:     Jinja/MapOfThy.thy
    Author:    Susannah Mansky, UIUC 2016
*)
(* HERE: this file can go elsewhere *)

section {* Some lemmas proving properties of map_of *}

theory MapOfThy
imports Main
begin

lemma map_of_set_pcs_notin: "C \<notin> (\<lambda>t. snd (fst t)) ` set FDTs \<Longrightarrow> map_of FDTs (F, C) = None"
  by (metis image_eqI image_image map_of_eq_None_iff snd_conv)

(*
(* HERE: these lemmas are based on similar from TypeRel - may wish to put those here *)

(* as in map_of_remap_SomeD *)
lemma map_of_insertmap_SomeD:
  "map_of (map (\<lambda>(F, y). (F, D, y)) fs) F = Some(C,y) \<Longrightarrow> map_of fs F = Some y"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)

lemma map_of_insertmap_SomeD2:
  "map_of (map (\<lambda>(F, y). (F, D, y)) fs) F = Some(C, b, T) \<Longrightarrow> map_of fs F = Some(b, T)"
 by (auto dest: map_of_insertmap_SomeD)
*)
lemma map_of_insertmap_SomeD':
  "map_of fs F = Some y \<Longrightarrow> map_of (map (\<lambda>(F, y). (F, D, y)) fs) F = Some(D,y)"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)
(*
lemma map_of_insertmap_SomeD2':
  "map_of fs F = Some(b, T) \<Longrightarrow> map_of (map (\<lambda>(F, y). (F, D, y)) fs) F = Some(D, b, T)"
 by (auto dest: map_of_insertmap_SomeD')

lemma map_of_insertmap_Some_eq:
  "map_of (map (\<lambda>(F, y). (F, D, y)) fs) F = Some (C', b, T) \<Longrightarrow> D = C'"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)
*)
lemma map_of_reinsert_neq_None:
  "Ca \<noteq> D \<Longrightarrow> map_of (map (\<lambda>(F, y). ((F, Ca), y)) fs) (F, D) = None"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)
(*
lemma map_of_insertmap_NoneD:
  "map_of (map (\<lambda>(F, y). (F, D, y)) fs) F = None \<Longrightarrow> map_of fs F = None"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)

lemma map_of_insertmap_NoneD':
  "map_of fs F = None \<Longrightarrow> map_of (map (\<lambda>(F, y). (F, D, y)) fs) F = None"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)
*)
lemma map_of_remap_insertmap:
  "map_of (map ((\<lambda>((F, D), b, T). (F, D, b, T)) \<circ> (\<lambda>(F, y). ((F, D), y))) fs)
    = map_of (map (\<lambda>(F, y). (F, D, y)) fs)"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)


lemma map_of_reinsert_SomeD:
  "map_of (map (\<lambda>(F, y). ((F, D), y)) fs) (F, D) = Some T \<Longrightarrow> map_of fs F = Some T"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)
(*
lemma map_of_reinsert_SomeD':
 "map_of fs F = Some T \<Longrightarrow> map_of (map (\<lambda>(F, y). ((F, D), y)) fs) (F, D) = Some T"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)


lemma map_of_const_remap_SomeD:
  "map_of t k = Some x \<Longrightarrow> map_of (map (\<lambda>(k, y). ((k, k'), y)) t) (k, k') = Some x"
(*<*)by (induct t) (auto simp:fun_upd_apply split: if_split_asm)(*>*)
*)
lemma map_of_filtered_SomeD:
"map_of fs (F,D) = Some (a, T) \<Longrightarrow> Q ((F,D),a,T) \<Longrightarrow>
       map_of (map (\<lambda>((F,D), b, T). ((F,D), P T)) (filter Q fs))
        (F,D) = Some (P T)"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)


lemma map_of_remove_filtered_SomeD:
"map_of fs (F,C) = Some (a, T) \<Longrightarrow> Q ((F,C),a,T) \<Longrightarrow>
       map_of (map (\<lambda>((F,D), b, T). (F, P T)) [((F, D), b, T)\<leftarrow>fs . Q ((F, D), b, T) \<and> D = C])
        F = Some (P T)"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)


(* HERE: clean up *)
lemma map_of_Some_None_split:
assumes "t = map (\<lambda>(F, y). ((F, C), y)) fs @ t'" "map_of t' (F, C) = None" "map_of t (F, C) = Some y"
shows "map_of (map (\<lambda>((F, D), b, T). (F, D, b, T)) t) F = Some (C, y)"
proof -
  have "map_of (map (\<lambda>(F, y). ((F, C), y)) fs) (F, C) = Some y" using assms by auto
  then have "\<forall>p. map_of fs F = Some p \<or> Some y \<noteq> Some p"
    by (metis map_of_reinsert_SomeD)
  then have "\<forall>f b p pa. ((f ++ map_of (map (\<lambda>(a, p). (a, b::'b, p)) fs)) F = Some p \<or> Some (b, pa) \<noteq> Some p)
     \<or> Some y \<noteq> Some pa"
    by (metis (no_types) map_add_find_right map_of_insertmap_SomeD')
  then have "(map_of (map (\<lambda>((a, b), c, d). (a, b, c, d)) t')
                     ++ map_of (map (\<lambda>(a, p). (a, C, p)) fs)) F = Some (C, y)"
    by blast
  then have "(map_of (map (\<lambda>((a, b), c, d). (a, b, c, d)) t')
      ++ map_of (map ((\<lambda>((a, b), c, d). (a, b, c, d)) \<circ> (\<lambda>(a, y). ((a, C), y))) fs)) F = Some (C, y)"
    by (simp add: map_of_remap_insertmap)
  then show ?thesis using assms by auto
qed

end