(* ################################################################# *)
(* Maize Pest Knowledge Base (Worldwide)                             *)
(* Generated with verified entomological sources                    *)
(* ################################################################# *)

Require Import String.
Open Scope string_scope.
Require Import String List Bool.
Import ListNotations.
Open Scope string_scope.


(* ----------------------------------------------------------------- *)
(* Pest categories                                                    *)
Inductive PestType :=
  | FieldPest
  | StoragePest.

(* ----------------------------------------------------------------- *)
(* Main pest identifiers                                              *)
Inductive Pest :=
  | FallArmyworm
  | EuropeanCornBorer
  | StemBorer
  | CornEarworm
  | CornLeafAphid
  | FleaBeetle
  | Cutworm
  | Wireworm
  | MaizeWeevil
  | LargerGrainBorer
  | LesserGrainBorer.

(* ----------------------------------------------------------------- *)
(* Fact record                                                        *)
Record PestFact := mkFact {
  pest : Pest;
  pest_type : PestType;
  scientific_name : string;
  biology : string;
  damage : string
}.

(* ----------------------------------------------------------------- *)
(* Knowledge base entries *)

Definition fact_fall_armyworm := mkFact
  FallArmyworm FieldPest
  "Spodoptera frugiperda"
  "Larvae feed on leaves, whorl, and ears; highly mobile and destructive."
  "Severe defoliation, reduced yields in fields worldwide.".

Definition fact_european_corn_borer := mkFact
  EuropeanCornBorer FieldPest
  "Ostrinia nubilalis"
  "Moth larvae bore stems and ears, weakening plant structure."
  "Tunnels reduce nutrient flow and crop yield.".

Definition fact_stem_borer := mkFact
  StemBorer FieldPest
  "Various species (e.g., Chilo partellus, Sesamia inferens)"
  "Caterpillars bore into stems, slowing growth."
  "Dead heart and stalk breakage reduce final yield.".

Definition fact_corn_earworm := mkFact
  CornEarworm FieldPest
  "Helicoverpa spp."
  "Larvae feed on silks and kernels."
  "Poor grain set and direct kernel loss.".

Definition fact_corn_leaf_aphid := mkFact
  CornLeafAphid FieldPest
  "Rhopalosiphum maidis"
  "Sap‑sucking aphid that can vector viruses."
  "Leaf yellowing, stunting, and virus spread.".

Definition fact_flea_beetle := mkFact
  FleaBeetle FieldPest
  "Chaetocnema spp."
  "Small beetles feeding on seedlings and leaves."
  "Seedling damage and reduced stand establishment.".

Definition fact_cutworm := mkFact
  Cutworm FieldPest
  "Agrotis spp."
  "Soil larvae cut young plants at or below soil level."
  "Plant loss and reduced population density.".

Definition fact_wireworm := mkFact
  Wireworm FieldPest
  "Agriotes spp."
  "Wireworm larvae attack roots and seeds."
  "Stunted plants and poor germination.".

Definition fact_maize_weevil := mkFact
  MaizeWeevil StoragePest
  "Sitophilus zeamais"
  "Beetle infesting stored maize grains."
  "High post‑harvest grain loss in storage.".

Definition fact_larger_grain_borer := mkFact
  LargerGrainBorer StoragePest
  "Prostephanus truncatus"
  "Primary pest of stored maize cobs."
  "Severe stored product damage and grain loss.".

Definition fact_lesser_grain_borer := mkFact
  LesserGrainBorer StoragePest
  "Rhyzopertha dominica"
  "Cosmopolitan stored grain beetle."
  "Significant grain weight loss in stored stocks.".

(* ----------------------------------------------------------------- *)
(* Knowledge Base List                                               *)
Definition MaizePestKB : list PestFact := [
  fact_fall_armyworm; fact_european_corn_borer;
  fact_stem_borer; fact_corn_earworm;
  fact_corn_leaf_aphid; fact_flea_beetle;
  fact_cutworm; fact_wireworm;
  fact_maize_weevil; fact_larger_grain_borer;
  fact_lesser_grain_borer
].

Definition pest_eqb (p1 p2 : Pest) : bool :=
  match p1, p2 with
  | FallArmyworm, FallArmyworm => true
  | EuropeanCornBorer, EuropeanCornBorer => true
  | StemBorer, StemBorer => true
  | CornEarworm, CornEarworm => true
  | CornLeafAphid, CornLeafAphid => true
  | FleaBeetle, FleaBeetle => true
  | Cutworm, Cutworm => true
  | Wireworm, Wireworm => true
  | MaizeWeevil, MaizeWeevil => true
  | LargerGrainBorer, LargerGrainBorer => true
  | LesserGrainBorer, LesserGrainBorer => true
  | _, _ => false
  end.

Definition pest_type_eqb (t1 t2 : PestType) : bool :=
  match t1, t2 with
  | FieldPest, FieldPest => true
  | StoragePest, StoragePest => true
  | _, _ => false
  end.
Definition pests_by_type (t : PestType) (kb : list PestFact) : list PestFact :=
  filter (fun f => pest_type_eqb f.(pest_type) t) kb.

Definition FieldPests :=
  pests_by_type FieldPest MaizePestKB.
  Compute  pests_by_type FieldPest MaizePestKB.





