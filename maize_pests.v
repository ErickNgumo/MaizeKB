(* ============================= *)
(* MAIZE PEST KNOWLEDGE BASE (Coq) *)
(* ============================= *)
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import String.

(* ===== BASIC TYPES ===== *)
Inductive PestType :=
  | Insect
  | Nematode
  | Vertebrate.

Inductive CropStage :=
  | Seed
  | Seedling
  | Vegetative
  | Reproductive
  | Storage.

Inductive PlantPart :=
  | Root
  | Stem
  | Leaf
  | Whorl
  | Cob
  | Grain.

Inductive Damage :=
  | Defoliation
  | SapLoss
  | StemTunneling
  | RootDamage
  | DeadHeart
  | Lodging
  | GrainLoss
  | QualityLoss
  | VirusTransmission.

Inductive DamageEffect :=
  | ReducedPhotosynthesis
  | PlantDeath
  | ReducedNutrientUptake
  | PoorGrainFilling
  | LodgingEffect
  | YieldLoss
  | QualityDeterioration
  | DiseaseSusceptibility.

(* ===== PESTS ===== *)
Inductive Pest :=
  | FallArmyworm
  | AfricanArmyworm
  | MaizeStalkBorer
  | SpottedStemBorer
  | PinkStemBorer
  | CornEarworm
  | Cutworm
  | Wireworm
  | WhiteGrub
  | Termite
  | ShootFly
  | Aphid
  | Leafhopper
  | Thrips
  | Whitefly
  | Grasshopper
  | Locust
  | Rootworm
  | NematodePest
  | MaizeWeevil
  | LargerGrainBorer
  | AngoumoisGrainMoth
  | FlourBeetle
  | Rodent
  | Bird.

  (* ===== SCIENTIFIC NAMES ===== *)
Definition pest_scientific_name (p : Pest) : string :=
  match p with
  | FallArmyworm => "Spodoptera frugiperda"
  | AfricanArmyworm => "Spodoptera exempta"
  | MaizeStalkBorer => "Busseola fusca"
  | SpottedStemBorer => "Chilo partellus"
  | PinkStemBorer => "Sesamia calamistis"
  | CornEarworm => "Helicoverpa zea"
  | Cutworm => "Agrotis spp."
  | Wireworm => "Elateridae spp."
  | WhiteGrub => "Phyllophaga spp."
  | Termite => "Macrotermes spp."
  | ShootFly => "Atherigona soccata"
  | Aphid => "Rhopalosiphum maidis"
  | Leafhopper => "Cicadulina spp."
  | Thrips => "Thrips tabaci"
  | Whitefly => "Bemisia tabaci"
  | Grasshopper => "Acrididae spp."
  | Locust => "Locusta migratoria"
  | Rootworm => "Diabrotica spp."
  | NematodePest => "Meloidogyne spp."
  | MaizeWeevil => "Sitophilus zeamais"
  | LargerGrainBorer => "Prostephanus truncatus"
  | AngoumoisGrainMoth => "Sitotroga cerealella"
  | FlourBeetle => "Tribolium spp."
  | Rodent => "Rattus rattus"
  | Bird => "Quelea quelea"
  end.


(* ===== CONTROL METHODS ===== *)
Inductive ControlMethod :=
  | Cultural
  | Biological
  | Chemical
  | Mechanical
  | Integrated.

Inductive Control :=
  | CropRotation
  | EarlyPlanting
  | FieldSanitation
  | HandPicking
  | NaturalEnemies
  | Biopesticides
  | ChemicalInsecticides
  | ResistantVarieties
  | PushPullSystem.

(* Map each control to its method *)
Definition control_method (c : Control) : ControlMethod :=
  match c with
  | CropRotation | EarlyPlanting | FieldSanitation | PushPullSystem => Cultural
  | NaturalEnemies | Biopesticides => Biological
  | ChemicalInsecticides => Chemical
  | HandPicking => Mechanical
  | ResistantVarieties => Integrated
  end.

(* Map pest to type *)
Definition pest_type (p : Pest) : PestType :=
  match p with
  | Rodent | Bird => Vertebrate
  | NematodePest => Nematode
  | _ => Insect
  end.

(* ===== ATTACK SITES ===== *)
Inductive attacks : Pest -> PlantPart -> Prop :=
  | FAW_attacks_leaf : attacks FallArmyworm Leaf
  | FAW_attacks_whorl : attacks FallArmyworm Whorl
  | FAW_attacks_cob : attacks FallArmyworm Cob
  | StalkBorer_attacks_stem : attacks MaizeStalkBorer Stem
  | SpottedBorer_attacks_stem : attacks SpottedStemBorer Stem
  | PinkBorer_attacks_stem : attacks PinkStemBorer Stem
  | Cutworm_attacks_stem : attacks Cutworm Stem
  | Wireworm_attacks_root : attacks Wireworm Root
  | WhiteGrub_attacks_root : attacks WhiteGrub Root
  | Termite_attacks_root : attacks Termite Root
  | Aphid_attacks_leaf : attacks Aphid Leaf
  | Leafhopper_attacks_leaf : attacks Leafhopper Leaf
  | Thrips_attacks_leaf : attacks Thrips Leaf
  | Whitefly_attacks_leaf : attacks Whitefly Leaf
  | Earworm_attacks_cob : attacks CornEarworm Cob
  | Weevil_attacks_grain : attacks MaizeWeevil Grain
  | LGB_attacks_grain : attacks LargerGrainBorer Grain
  | AGM_attacks_grain : attacks AngoumoisGrainMoth Grain
  | FlourBeetle_attacks_grain : attacks FlourBeetle Grain
  | Rodent_attacks_grain : attacks Rodent Grain
  | Bird_attacks_cob : attacks Bird Cob.

(* ===== DAMAGE CAUSED ===== *)
Inductive causes : Pest -> Damage -> Prop :=
  | FAW_causes_defoliation : causes FallArmyworm Defoliation
  | AfricanArmyworm_causes_defoliation : causes AfricanArmyworm Defoliation
  | StalkBorer_causes_tunnel : causes MaizeStalkBorer StemTunneling
  | StalkBorer_causes_deadheart : causes MaizeStalkBorer DeadHeart
  | StalkBorer_causes_lodging : causes MaizeStalkBorer Lodging
  | Cutworm_causes_deadheart : causes Cutworm DeadHeart
  | Wireworm_causes_root : causes Wireworm RootDamage
  | WhiteGrub_causes_root : causes WhiteGrub RootDamage
  | Termite_causes_root : causes Termite RootDamage
  | ShootFly_causes_deadheart : causes ShootFly DeadHeart
  | Aphid_causes_sap : causes Aphid SapLoss
  | Aphid_causes_virus : causes Aphid VirusTransmission
  | Leafhopper_causes_virus : causes Leafhopper VirusTransmission
  | Thrips_causes_sap : causes Thrips SapLoss
  | Whitefly_causes_sap : causes Whitefly SapLoss
  | Grasshopper_causes_defoliation : causes Grasshopper Defoliation
  | Locust_causes_defoliation : causes Locust Defoliation
  | Rootworm_causes_root : causes Rootworm RootDamage
  | Nematode_causes_root : causes NematodePest RootDamage
  | Weevil_causes_grain : causes MaizeWeevil GrainLoss
  | LGB_causes_grain : causes LargerGrainBorer GrainLoss
  | AGM_causes_quality : causes AngoumoisGrainMoth QualityLoss
  | FlourBeetle_causes_quality : causes FlourBeetle QualityLoss
  | Rodent_causes_grain : causes Rodent GrainLoss
  | Bird_causes_cob : causes Bird GrainLoss.

(* ===== CROP STAGES AFFECTED ===== *)
Inductive affects_stage : Pest -> CropStage -> Prop :=
  | FAW_veg : affects_stage FallArmyworm Vegetative
  | FAW_rep : affects_stage FallArmyworm Reproductive
  | Cutworm_seedling : affects_stage Cutworm Seedling
  | Wireworm_seed : affects_stage Wireworm Seed
  | Weevil_storage : affects_stage MaizeWeevil Storage
  | LGB_storage : affects_stage LargerGrainBorer Storage
  | AGM_storage : affects_stage AngoumoisGrainMoth Storage
  | Rodent_storage : affects_stage Rodent Storage.

(* ===== DAMAGE → EFFECT ===== *)
Inductive damage_effect : Damage -> DamageEffect -> Prop :=
  | Defoliation_causes_photo : damage_effect Defoliation ReducedPhotosynthesis
  | Defoliation_causes_yield : damage_effect Defoliation YieldLoss
  | StemTunneling_causes_lodging : damage_effect StemTunneling LodgingEffect
  | StemTunneling_causes_yield : damage_effect StemTunneling YieldLoss
  | RootDamage_causes_nutrient : damage_effect RootDamage ReducedNutrientUptake
  | RootDamage_causes_death : damage_effect RootDamage PlantDeath
  | DeadHeart_causes_death : damage_effect DeadHeart PlantDeath
  | SapLoss_causes_yield : damage_effect SapLoss YieldLoss
  | VirusTransmission_causes_yield : damage_effect VirusTransmission YieldLoss
  | GrainLoss_causes_yield : damage_effect GrainLoss YieldLoss
  | QualityLoss_causes_quality : damage_effect QualityLoss QualityDeterioration.

(* ===== PEST → EFFECT (Derived) ===== *)
Definition causes_effect (p : Pest) (e : DamageEffect) : Prop :=
  exists d, causes p d /\ damage_effect d e.

(* ===== PEST → CONTROL ===== *)

Definition pest_controls (p : Pest) : list Control :=
  match p with
  | FallArmyworm => [ChemicalInsecticides; NaturalEnemies; PushPullSystem]
  | MaizeStalkBorer => [CropRotation]
  | Aphid => [NaturalEnemies]
  | MaizeWeevil => [FieldSanitation]
  | _ => []
  end.



(* ===== FACT RECORD (FOR STREAMLIT DISPLAY) ===== *)
Inductive PestCategory := FieldPest | StoragePest | VertebratePest.

Record Fact := mkFact {
  pest_name : Pest;
  pest_class : PestCategory;
  scientific_name : string;
  description : string;
  damage_summary : string
}.

  Record PestProfile := mkProfile {
  pest_common : Pest;
  pest_scientific : string;
  pest_type_info : PestType;
  damage_effects : list DamageEffect;
  plant_parts_attacked : list PlantPart;
  crop_stages_affected : list CropStage;
  control_actions : list Control;
  control_methods_general : list ControlMethod
}.



(* ===== FACTS ===== *)

Definition FAW_fact : Fact :=
  mkFact
    FallArmyworm
    FieldPest
    "Spodoptera frugiperda"
    "Larvae feed on leaves, whorl, and ears; highly mobile and destructive."
    "Causes severe defoliation and reduced yields in maize fields worldwide.".

Definition AfricanArmyworm_fact : Fact :=
  mkFact
    AfricanArmyworm
    FieldPest
    "Spodoptera exempta"
    "Larvae feed on maize leaves, sometimes leading to complete defoliation."
    "Causes defoliation and yield loss.".

Definition StalkBorer_fact : Fact :=
  mkFact
    MaizeStalkBorer
    FieldPest
    "Busseola fusca"
    "Larvae bore into maize stems, causing deadheart and lodging."
    "Stem tunneling, deadheart, lodging, reduced nutrient uptake, yield loss.".

Definition SpottedBorer_fact : Fact :=
  mkFact
    SpottedStemBorer
    FieldPest
    "Chilo partellus"
    "Stem borer larvae bore maize stems, affecting plant growth."
    "Stem damage and lodging, reduced yield.".

Definition PinkBorer_fact : Fact :=
  mkFact
    PinkStemBorer
    FieldPest
    "Sesamia calamistis"
    "Bores into maize stems causing stem tunneling and plant weakening."
    "Stem tunneling, deadheart, lodging, yield loss.".

Definition CornEarworm_fact : Fact :=
  mkFact
    CornEarworm
    FieldPest
    "Helicoverpa zea"
    "Larvae feed on maize cobs, reducing kernel quality."
    "Cob damage, grain loss, reduced yield.".

Definition Cutworm_fact : Fact :=
  mkFact
    Cutworm
    FieldPest
    "Agrotis spp."
    "Larvae cut seedlings at soil level, causing deadheart in young plants."
    "Deadheart, reduced establishment, yield loss.".

Definition Wireworm_fact : Fact :=
  mkFact
    Wireworm
    FieldPest
    "Elateridae spp."
    "Larvae feed on maize roots, stunting plant growth."
    "Root damage, reduced nutrient uptake, plant death, yield loss.".

Definition WhiteGrub_fact : Fact :=
  mkFact
    WhiteGrub
    FieldPest
    "Phyllophaga spp."
    "Larvae feed on maize roots, leading to poor growth."
    "Root damage, stunted plants, yield loss.".

Definition Termite_fact : Fact :=
  mkFact
    Termite
    FieldPest
    "Macrotermes spp."
    "Feed on maize roots and stems, weakening plants."
    "Root and stem damage, plant death, yield loss.".

Definition ShootFly_fact : Fact :=
  mkFact
    ShootFly
    FieldPest
    "Atherigona soccata"
    "Larvae feed in the central whorl causing deadheart."
    "Deadheart formation, reduced yield.".

Definition Aphid_fact : Fact :=
  mkFact
    Aphid
    FieldPest
    "Rhopalosiphum maidis"
    "Suck sap from maize leaves and transmit viruses."
    "Sap loss, virus transmission, yield reduction.".

Definition Leafhopper_fact : Fact :=
  mkFact
    Leafhopper
    FieldPest
    "Cicadulina spp."
    "Sucks sap and transmits maize streak virus."
    "Virus transmission, stunted growth, yield loss.".

Definition Thrips_fact : Fact :=
  mkFact
    Thrips
    FieldPest
    "Thrips tabaci"
    "Feed on leaf tissues causing silvering and sap loss."
    "Sap loss, reduced photosynthesis, yield loss.".

Definition Whitefly_fact : Fact :=
  mkFact
    Whitefly
    FieldPest
    "Bemisia tabaci"
    "Feeds on maize leaves and transmits viruses."
    "Sap loss, virus transmission, reduced yield.".

Definition Grasshopper_fact : Fact :=
  mkFact
    Grasshopper
    FieldPest
    "Acrididae spp."
    "Feeds on maize leaves, sometimes causing defoliation."
    "Defoliation and reduced photosynthesis.".

Definition Locust_fact : Fact :=
  mkFact
    Locust
    FieldPest
    "Locusta migratoria"
    "Feeds on maize leaves in swarms."
    "Severe defoliation, reduced yield.".

Definition Rootworm_fact : Fact :=
  mkFact
    Rootworm
    FieldPest
    "Diabrotica spp."
    "Larvae feed on roots, weakening plants."
    "Root damage, plant death, yield reduction.".

Definition Nematode_fact : Fact :=
  mkFact
    NematodePest
    FieldPest
    "Meloidogyne spp."
    "Root-knot nematodes damage maize roots."
    "Root damage, stunted growth, yield loss.".

Definition MaizeWeevil_fact : Fact :=
  mkFact
    MaizeWeevil
    StoragePest
    "Sitophilus zeamais"
    "Infests stored maize grains causing weight loss."
    "Grain loss, reduced quality, post-harvest losses.".

Definition LGB_fact : Fact :=
  mkFact
    LargerGrainBorer
    StoragePest
    "Prostephanus truncatus"
    "Infests stored maize grains, tunneling kernels."
    "Grain loss, reduced quality, post-harvest losses.".

Definition AGM_fact : Fact :=
  mkFact
    AngoumoisGrainMoth
    StoragePest
    "Sitotroga cerealella"
    "Infests stored maize grains; larvae feed inside kernels."
    "Grain loss, quality deterioration.".

Definition FlourBeetle_fact : Fact :=
  mkFact
    FlourBeetle
    StoragePest
    "Tribolium spp."
    "Attacks stored maize grains and flour products."
    "Grain loss, quality deterioration.".

Definition Rodent_fact : Fact :=
  mkFact
    Rodent
    VertebratePest
    "Rattus rattus"
    "Feeds on stored and field maize grains."
    "Grain loss, reduced yield.".

Definition Bird_fact : Fact :=
  mkFact
    Bird
    VertebratePest
    "Quelea quelea"
    "Feeds on maize grains in the field and storage."
    "Grain loss, yield reduction.".







  (* ================== *)
(* ===== Query Engines ===== *)




Definition all_pests : list Pest :=
  [ FallArmyworm; AfricanArmyworm; MaizeStalkBorer; SpottedStemBorer; PinkStemBorer;
    CornEarworm; Cutworm; Wireworm; WhiteGrub; Termite; ShootFly; Aphid;
    Leafhopper; Thrips; Whitefly; Grasshopper; Locust; Rootworm; NematodePest;
    MaizeWeevil; LargerGrainBorer; AngoumoisGrainMoth; FlourBeetle; Rodent; Bird ].

(* Helper booleans *)

Definition causes_effect_dec (p : Pest) (e : DamageEffect) : bool :=
  match p, e with
  | FallArmyworm, ReducedPhotosynthesis => true
  | FallArmyworm, YieldLoss => true
  | AfricanArmyworm, ReducedPhotosynthesis => true
  | AfricanArmyworm, YieldLoss => true
  | MaizeStalkBorer, YieldLoss => true
  | MaizeStalkBorer, LodgingEffect => true
  | Cutworm, YieldLoss => true
  | Wireworm, ReducedNutrientUptake => true
  | Wireworm, PlantDeath => true
  | WhiteGrub, ReducedNutrientUptake => true
  | WhiteGrub, PlantDeath => true
  | Termite, ReducedNutrientUptake => true
  | Termite, PlantDeath => true
  | ShootFly, PlantDeath => true
  | Aphid, YieldLoss => true
  | Leafhopper, YieldLoss => true
  | Thrips, YieldLoss => true
  | Whitefly, YieldLoss => true
  | Grasshopper, ReducedPhotosynthesis => true
  | Grasshopper, YieldLoss => true
  | Locust, ReducedPhotosynthesis => true
  | Locust, YieldLoss => true
  | Rootworm, ReducedNutrientUptake => true
  | Rootworm, PlantDeath => true
  | NematodePest, ReducedNutrientUptake => true
  | NematodePest, PlantDeath => true
  | MaizeWeevil, YieldLoss => true
  | LargerGrainBorer, YieldLoss => true
  | AngoumoisGrainMoth, QualityDeterioration => true
  | FlourBeetle, QualityDeterioration => true
  | Rodent, YieldLoss => true
  | Bird, YieldLoss => true
  | _, _ => false
  end.

Definition pest_attacks_part_dec (p : Pest) (part : PlantPart) : bool :=
  match p, part with
  | FallArmyworm, Leaf => true
  | FallArmyworm, Whorl => true
  | FallArmyworm, Cob => true
  | MaizeStalkBorer, Stem => true
  | SpottedStemBorer, Stem => true
  | PinkStemBorer, Stem => true
  | Cutworm, Stem => true
  | Wireworm, Root => true
  | WhiteGrub, Root => true
  | Termite, Root => true
  | Aphid, Leaf => true
  | Leafhopper, Leaf => true
  | Thrips, Leaf => true
  | Whitefly, Leaf => true
  | CornEarworm, Cob => true
  | MaizeWeevil, Grain => true
  | LargerGrainBorer, Grain => true
  | AngoumoisGrainMoth, Grain => true
  | FlourBeetle, Grain => true
  | Rodent, Grain => true
  | Bird, Cob => true
  | _, _ => false
  end.

Definition pest_affects_stage_dec (p : Pest) (s : CropStage) : bool :=
  match p, s with
  | FallArmyworm, Vegetative => true
  | FallArmyworm, Reproductive => true
  | Cutworm, Seedling => true
  | Wireworm, Seed => true
  | MaizeWeevil, Storage => true
  | LargerGrainBorer, Storage => true
  | AngoumoisGrainMoth, Storage => true
  | Rodent, Storage => true
  | _, _ => false
  end.


(* -------Query Functions---------------*)

(* Damage effects for a pest *)
Definition pest_damage_effects (p : Pest) : list DamageEffect :=
  filter (fun e => causes_effect_dec p e) 
         [ReducedPhotosynthesis; PlantDeath; YieldLoss; QualityDeterioration; LodgingEffect; ReducedNutrientUptake].

(* Plant parts attacked by a pest *)
Definition pest_attacks_parts (p : Pest) : list PlantPart :=
  filter (fun part => pest_attacks_part_dec p part) [Root; Stem; Leaf; Whorl; Cob; Grain].

(* Crop stages affected by a pest *)
Definition pest_stages_affected (p : Pest) : list CropStage :=
  filter (fun s => pest_affects_stage_dec p s) [Seed; Seedling; Vegetative; Reproductive; Storage].


Definition pests_causing_effect (e : DamageEffect) : list Pest :=
  filter (fun p => causes_effect_dec p e) all_pests.

Definition pests_attacking_part (part : PlantPart) : list Pest :=
  filter (fun p => pest_attacks_part_dec p part) all_pests.

Definition pests_affecting_stage (s : CropStage) : list Pest :=
  filter (fun p => pest_affects_stage_dec p s) all_pests.

Definition pests_by_effect_and_part (e : DamageEffect) (part : PlantPart) : list Pest :=
  filter (fun p => causes_effect_dec p e && pest_attacks_part_dec p part) all_pests.

Definition controls_for_pest_list (p : Pest) : list Control :=
  pest_controls p.

  Definition pest_profile (p : Pest) (sci_name : string) : PestProfile :=
  mkProfile
    p
    sci_name
    (pest_type p)
    (pest_damage_effects p)
    (pest_attacks_parts p)
    (pest_stages_affected p)
    (pest_controls p)
    (map control_method (pest_controls p)).

(* Example Queries *)

(* Compute all pests causing YieldLoss *)
Compute pests_causing_effect YieldLoss.
(* Compute pests causing YieldLoss AND attacking Cob *)
Compute pests_by_effect_and_part YieldLoss Cob.
(* ---------- DAMAGE EFFECT QUERIES ---------- *)

(* All pests causing YieldLoss *)
Compute pests_causing_effect YieldLoss.

(* All pests causing ReducedPhotosynthesis *)
Compute pests_causing_effect ReducedPhotosynthesis.

(* All pests causing PlantDeath *)
Compute pests_causing_effect PlantDeath.

(* All pests causing QualityDeterioration *)
Compute pests_causing_effect QualityDeterioration.

(* ---------- PLANT PART QUERIES ---------- *)

(* All pests attacking Cob *)
Compute pests_attacking_part Cob.

(* All pests attacking Leaf *)
Compute pests_attacking_part Leaf.

(* All pests attacking Stem *)
Compute pests_attacking_part Stem.

(* All pests attacking Root *)
Compute pests_attacking_part Root.

(* ---------- CROP STAGE QUERIES ---------- *)

(* All pests affecting Seed stage *)
Compute pests_affecting_stage Seed.

(* All pests affecting Seedling stage *)
Compute pests_affecting_stage Seedling.

(* All pests affecting Vegetative stage *)
Compute pests_affecting_stage Vegetative.

(* All pests affecting Reproductive stage *)
Compute pests_affecting_stage Reproductive.

(* All pests affecting Storage stage *)
Compute pests_affecting_stage Storage.

(* ---------- CONTROL QUERIES ---------- *)

(* All control actions for FallArmyworm *)
Compute controls_for_pest_list FallArmyworm.

(* All control actions for MaizeStalkBorer *)
Compute controls_for_pest_list MaizeStalkBorer.

(* All control actions for Aphid *)
Compute controls_for_pest_list Aphid.

(* Map the controls of FallArmyworm to general control methods *)
Compute map control_method (controls_for_pest_list FallArmyworm).

(* ---------- PEST TYPE QUERIES ---------- *)

(* Type of FallArmyworm *)
Compute pest_type FallArmyworm.

(* Type of Rodent *)
Compute pest_type Rodent.

(* Type of NematodePest *)
Compute pest_type NematodePest.



(* Pests causing YieldLoss AND attacking Cob *)
Compute pests_by_effect_and_part YieldLoss Cob.

(* Pests causing ReducedPhotosynthesis AND attacking Leaf *)
Compute pests_by_effect_and_part ReducedPhotosynthesis Leaf.

(* Pests causing PlantDeath AND attacking Root *)
Compute pests_by_effect_and_part PlantDeath Root.


(* Pests causing YieldLoss AND affecting Storage stage *)
Compute filter (fun p => causes_effect_dec p YieldLoss && pest_affects_stage_dec p Storage) all_pests.

(* Pests attacking Grain AND having YieldLoss effect *)
Compute filter (fun p => pest_attacks_part_dec p Grain && causes_effect_dec p YieldLoss) all_pests.

Compute pest_profile FallArmyworm "Spodoptera frugiperda".
Compute pest_profile MaizeStalkBorer "Busseola fusca".
Compute pest_profile Aphid "Rhopalosiphum maidis".


