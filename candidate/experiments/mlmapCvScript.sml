(* mlstring-keyed finite maps used by Pancake's globals pass. *)
Theory mlmapCv
Ancestors panSimplifyCv cv_string_fmap
Libs preamble cv_transLib

Theorem explode_inj[simp]:
  INJ explode s UNIV
Proof
  simp [INJ_DEF]
QED

Theorem implode_inj[simp]:
  INJ implode s UNIV
Proof
  simp [INJ_DEF]
QED

Theorem mlmap_roundtrip:
  !m. MAP_KEYS implode (MAP_KEYS explode m) = m
Proof
  ho_match_mp_tac fmap_INDUCT >> rw [] >>
  simp [MAP_KEYS_FUPDATE]
QED

Definition from_mlmap_def:
  from_mlmap f (m : mlstring |-> 'a) =
    from_string_fmap f (MAP_KEYS explode m)
End
Definition to_mlmap_def:
  to_mlmap t v = MAP_KEYS implode (to_string_fmap t v)
End

Theorem from_to_mlmap[cv_from_to]:
  from_to f t ==> from_to (from_mlmap f) (to_mlmap t)
Proof
  strip_tac >> drule from_to_string_fmap >>
  rw [cv_typeTheory.from_to_def, from_mlmap_def, to_mlmap_def] >>
  simp [mlmap_roundtrip]
QED

Theorem mlstring_key_rep:
  from_list from_char (explode k) =
  cv_snd (from_mlstring_mlstring_mlstring k)
Proof
  Cases_on `k` >> simp [basis_cvTheory.from_mlstring_mlstring_def]
QED

Theorem cv_mlmap_empty[cv_rep]:
  from_mlmap f FEMPTY = cv$Num 0
Proof
  simp [from_mlmap_def, cv_rep_string_FEMPTY]
QED

Theorem cv_mlmap_lookup[cv_rep]:
  from_option f (FLOOKUP m k) =
  cv_st_get (from_mlmap f m)
    (cv_snd (from_mlstring_mlstring_mlstring k))
Proof
  simp [from_mlmap_def, GSYM mlstring_key_rep,
        GSYM cv_rep_string_FLOOKUP, FLOOKUP_MAP_KEYS_MAPPED]
QED

Theorem cv_mlmap_update[cv_rep]:
  from_mlmap f (m |+ (k,v)) =
  cv_st_set (from_mlmap f m)
    (cv_snd (from_mlstring_mlstring_mlstring k)) (f v)
Proof
  simp [from_mlmap_def, MAP_KEYS_FUPDATE,
        cv_rep_string_FUPDATE, mlstring_key_rep]
QED
