"""
Maize Pest Profiles - Python Interface to Coq Knowledge Base
This module provides Python access to the formally verified pest knowledge defined in maize_pests.v

Based on the Coq definitions from maize_pests.v
"""

from enum import Enum, auto
from typing import List, Set, Dict
from dataclasses import dataclass


# ===== ENUMERATIONS (matching Coq definitions) =====

class PestType(Enum):
    """Corresponds to PestType in maize_pests.v"""
    INSECT = auto()
    NEMATODE = auto()
    VERTEBRATE = auto()


class PestCategory(Enum):
    """Corresponds to PestCategory in maize_pests.v"""
    FIELD_PEST = "FieldPest"
    STORAGE_PEST = "StoragePest"
    VERTEBRATE_PEST = "VertebratePest"


class CropStage(Enum):
    """Corresponds to CropStage in maize_pests.v"""
    SEED = auto()
    SEEDLING = auto()
    VEGETATIVE = auto()
    REPRODUCTIVE = auto()
    STORAGE = auto()


class PlantPart(Enum):
    """Corresponds to PlantPart in maize_pests.v"""
    ROOT = auto()
    STEM = auto()
    LEAF = auto()
    WHORL = auto()
    COB = auto()
    GRAIN = auto()


class Damage(Enum):
    """Corresponds to Damage in maize_pests.v"""
    DEFOLIATION = auto()
    SAP_LOSS = auto()
    STEM_TUNNELING = auto()
    ROOT_DAMAGE = auto()
    DEAD_HEART = auto()
    LODGING = auto()
    GRAIN_LOSS = auto()
    QUALITY_LOSS = auto()
    VIRUS_TRANSMISSION = auto()


class DamageEffect(Enum):
    """Corresponds to DamageEffect in maize_pests.v"""
    REDUCED_PHOTOSYNTHESIS = auto()
    PLANT_DEATH = auto()
    REDUCED_NUTRIENT_UPTAKE = auto()
    POOR_GRAIN_FILLING = auto()
    LODGING_EFFECT = auto()
    YIELD_LOSS = auto()
    QUALITY_DETERIORATION = auto()
    DISEASE_SUSCEPTIBILITY = auto()


class ControlMethod(Enum):
    """Corresponds to ControlMethod in maize_pests.v"""
    CULTURAL = auto()
    BIOLOGICAL = auto()
    CHEMICAL = auto()
    MECHANICAL = auto()
    INTEGRATED = auto()


class Control(Enum):
    """Corresponds to Control actions in maize_pests.v"""
    CROP_ROTATION = auto()
    EARLY_PLANTING = auto()
    FIELD_SANITATION = auto()
    HAND_PICKING = auto()
    NATURAL_ENEMIES = auto()
    BIOPESTICIDES = auto()
    CHEMICAL_INSECTICIDES = auto()
    RESISTANT_VARIETIES = auto()
    PUSH_PULL_SYSTEM = auto()


# ===== CONTROL METHOD MAPPING =====
# Corresponds to control_method function in maize_pests.v

CONTROL_TO_METHOD = {
    Control.CROP_ROTATION: ControlMethod.CULTURAL,
    Control.EARLY_PLANTING: ControlMethod.CULTURAL,
    Control.FIELD_SANITATION: ControlMethod.CULTURAL,
    Control.PUSH_PULL_SYSTEM: ControlMethod.CULTURAL,
    Control.NATURAL_ENEMIES: ControlMethod.BIOLOGICAL,
    Control.BIOPESTICIDES: ControlMethod.BIOLOGICAL,
    Control.CHEMICAL_INSECTICIDES: ControlMethod.CHEMICAL,
    Control.HAND_PICKING: ControlMethod.MECHANICAL,
    Control.RESISTANT_VARIETIES: ControlMethod.INTEGRATED,
}


# ===== PEST PROFILES =====
# Corresponds to Fact records and derived profiles in maize_pests.v

PEST_PROFILES = {
    'FallArmyworm': {
        'common_name': 'Fall Armyworm',
        'scientific_name': 'Spodoptera frugiperda',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae feed on leaves, whorl, and ears; highly mobile and destructive.',
        'damage_summary': 'Causes severe defoliation and reduced yields in maize fields worldwide.',
        'plant_parts_attacked': [PlantPart.LEAF, PlantPart.WHORL, PlantPart.COB],
        'crop_stages_affected': [CropStage.VEGETATIVE, CropStage.REPRODUCTIVE],
        'damage_types': [Damage.DEFOLIATION],
        'damage_effects': [DamageEffect.REDUCED_PHOTOSYNTHESIS, DamageEffect.YIELD_LOSS],
        'control_actions': [Control.CHEMICAL_INSECTICIDES, Control.NATURAL_ENEMIES, Control.PUSH_PULL_SYSTEM],
        'control_methods_general': [ControlMethod.CHEMICAL, ControlMethod.BIOLOGICAL, ControlMethod.CULTURAL]
    },
    
    'AfricanArmyworm': {
        'common_name': 'African Armyworm',
        'scientific_name': 'Spodoptera exempta',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae feed on maize leaves, sometimes leading to complete defoliation.',
        'damage_summary': 'Causes defoliation and yield loss.',
        'plant_parts_attacked': [PlantPart.LEAF],
        'crop_stages_affected': [CropStage.VEGETATIVE],
        'damage_types': [Damage.DEFOLIATION],
        'damage_effects': [DamageEffect.REDUCED_PHOTOSYNTHESIS, DamageEffect.YIELD_LOSS],
        'control_actions': [Control.CHEMICAL_INSECTICIDES, Control.HAND_PICKING],
        'control_methods_general': [ControlMethod.CHEMICAL, ControlMethod.MECHANICAL]
    },
    
    'MaizeStalkBorer': {
        'common_name': 'Maize Stalk Borer',
        'scientific_name': 'Busseola fusca',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae bore into maize stems, causing deadheart and lodging.',
        'damage_summary': 'Stem tunneling, deadheart, lodging, reduced nutrient uptake, yield loss.',
        'plant_parts_attacked': [PlantPart.STEM],
        'crop_stages_affected': [CropStage.VEGETATIVE, CropStage.REPRODUCTIVE],
        'damage_types': [Damage.STEM_TUNNELING, Damage.DEAD_HEART, Damage.LODGING],
        'damage_effects': [DamageEffect.LODGING_EFFECT, DamageEffect.YIELD_LOSS],
        'control_actions': [Control.CROP_ROTATION],
        'control_methods_general': [ControlMethod.CULTURAL]
    },
    
    'SpottedStemBorer': {
        'common_name': 'Spotted Stem Borer',
        'scientific_name': 'Chilo partellus',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Stem borer larvae bore maize stems, affecting plant growth.',
        'damage_summary': 'Stem damage and lodging, reduced yield.',
        'plant_parts_attacked': [PlantPart.STEM],
        'crop_stages_affected': [CropStage.VEGETATIVE, CropStage.REPRODUCTIVE],
        'damage_types': [Damage.STEM_TUNNELING],
        'damage_effects': [DamageEffect.LODGING_EFFECT, DamageEffect.YIELD_LOSS],
        'control_actions': [Control.CROP_ROTATION, Control.RESISTANT_VARIETIES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.INTEGRATED]
    },
    
    'PinkStemBorer': {
        'common_name': 'Pink Stem Borer',
        'scientific_name': 'Sesamia calamistis',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Bores into maize stems causing stem tunneling and plant weakening.',
        'damage_summary': 'Stem tunneling, deadheart, lodging, yield loss.',
        'plant_parts_attacked': [PlantPart.STEM],
        'crop_stages_affected': [CropStage.VEGETATIVE, CropStage.REPRODUCTIVE],
        'damage_types': [Damage.STEM_TUNNELING, Damage.DEAD_HEART],
        'damage_effects': [DamageEffect.LODGING_EFFECT, DamageEffect.YIELD_LOSS],
        'control_actions': [Control.FIELD_SANITATION, Control.CHEMICAL_INSECTICIDES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.CHEMICAL]
    },
    
    'CornEarworm': {
        'common_name': 'Corn Earworm',
        'scientific_name': 'Helicoverpa zea',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae feed on maize cobs, reducing kernel quality.',
        'damage_summary': 'Cob damage, grain loss, reduced yield.',
        'plant_parts_attacked': [PlantPart.COB],
        'crop_stages_affected': [CropStage.REPRODUCTIVE],
        'damage_types': [Damage.GRAIN_LOSS],
        'damage_effects': [DamageEffect.YIELD_LOSS, DamageEffect.QUALITY_DETERIORATION],
        'control_actions': [Control.CHEMICAL_INSECTICIDES, Control.HAND_PICKING],
        'control_methods_general': [ControlMethod.CHEMICAL, ControlMethod.MECHANICAL]
    },
    
    'Cutworm': {
        'common_name': 'Cutworm',
        'scientific_name': 'Agrotis spp.',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae cut seedlings at soil level, causing deadheart in young plants.',
        'damage_summary': 'Deadheart, reduced establishment, yield loss.',
        'plant_parts_attacked': [PlantPart.STEM],
        'crop_stages_affected': [CropStage.SEEDLING],
        'damage_types': [Damage.DEAD_HEART],
        'damage_effects': [DamageEffect.PLANT_DEATH, DamageEffect.YIELD_LOSS],
        'control_actions': [Control.HAND_PICKING, Control.CHEMICAL_INSECTICIDES],
        'control_methods_general': [ControlMethod.MECHANICAL, ControlMethod.CHEMICAL]
    },
    
    'Wireworm': {
        'common_name': 'Wireworm',
        'scientific_name': 'Elateridae spp.',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae feed on maize roots, stunting plant growth.',
        'damage_summary': 'Root damage, reduced nutrient uptake, plant death, yield loss.',
        'plant_parts_attacked': [PlantPart.ROOT],
        'crop_stages_affected': [CropStage.SEED, CropStage.SEEDLING],
        'damage_types': [Damage.ROOT_DAMAGE],
        'damage_effects': [DamageEffect.REDUCED_NUTRIENT_UPTAKE, DamageEffect.PLANT_DEATH],
        'control_actions': [Control.CROP_ROTATION, Control.CHEMICAL_INSECTICIDES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.CHEMICAL]
    },
    
    'WhiteGrub': {
        'common_name': 'White Grub',
        'scientific_name': 'Phyllophaga spp.',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae feed on maize roots, leading to poor growth.',
        'damage_summary': 'Root damage, stunted plants, yield loss.',
        'plant_parts_attacked': [PlantPart.ROOT],
        'crop_stages_affected': [CropStage.SEEDLING, CropStage.VEGETATIVE],
        'damage_types': [Damage.ROOT_DAMAGE],
        'damage_effects': [DamageEffect.REDUCED_NUTRIENT_UPTAKE, DamageEffect.PLANT_DEATH],
        'control_actions': [Control.CROP_ROTATION, Control.HAND_PICKING],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.MECHANICAL]
    },
    
    'Termite': {
        'common_name': 'Termite',
        'scientific_name': 'Macrotermes spp.',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Feed on maize roots and stems, weakening plants.',
        'damage_summary': 'Root and stem damage, plant death, yield loss.',
        'plant_parts_attacked': [PlantPart.ROOT, PlantPart.STEM],
        'crop_stages_affected': [CropStage.SEEDLING, CropStage.VEGETATIVE],
        'damage_types': [Damage.ROOT_DAMAGE],
        'damage_effects': [DamageEffect.REDUCED_NUTRIENT_UPTAKE, DamageEffect.PLANT_DEATH],
        'control_actions': [Control.FIELD_SANITATION, Control.CHEMICAL_INSECTICIDES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.CHEMICAL]
    },
    
    'ShootFly': {
        'common_name': 'Shoot Fly',
        'scientific_name': 'Atherigona soccata',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae feed in the central whorl causing deadheart.',
        'damage_summary': 'Deadheart formation, reduced yield.',
        'plant_parts_attacked': [PlantPart.WHORL],
        'crop_stages_affected': [CropStage.SEEDLING],
        'damage_types': [Damage.DEAD_HEART],
        'damage_effects': [DamageEffect.PLANT_DEATH],
        'control_actions': [Control.EARLY_PLANTING, Control.CHEMICAL_INSECTICIDES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.CHEMICAL]
    },
    
    'Aphid': {
        'common_name': 'Corn Leaf Aphid',
        'scientific_name': 'Rhopalosiphum maidis',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Suck sap from maize leaves and transmit viruses.',
        'damage_summary': 'Sap loss, virus transmission, yield reduction.',
        'plant_parts_attacked': [PlantPart.LEAF],
        'crop_stages_affected': [CropStage.VEGETATIVE, CropStage.REPRODUCTIVE],
        'damage_types': [Damage.SAP_LOSS, Damage.VIRUS_TRANSMISSION],
        'damage_effects': [DamageEffect.YIELD_LOSS],
        'control_actions': [Control.NATURAL_ENEMIES],
        'control_methods_general': [ControlMethod.BIOLOGICAL]
    },
    
    'Leafhopper': {
        'common_name': 'Leafhopper',
        'scientific_name': 'Cicadulina spp.',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Sucks sap and transmits maize streak virus.',
        'damage_summary': 'Virus transmission, stunted growth, yield loss.',
        'plant_parts_attacked': [PlantPart.LEAF],
        'crop_stages_affected': [CropStage.VEGETATIVE],
        'damage_types': [Damage.VIRUS_TRANSMISSION],
        'damage_effects': [DamageEffect.YIELD_LOSS],
        'control_actions': [Control.CHEMICAL_INSECTICIDES, Control.RESISTANT_VARIETIES],
        'control_methods_general': [ControlMethod.CHEMICAL, ControlMethod.INTEGRATED]
    },
    
    'Thrips': {
        'common_name': 'Thrips',
        'scientific_name': 'Thrips tabaci',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Feed on leaf tissues causing silvering and sap loss.',
        'damage_summary': 'Sap loss, reduced photosynthesis, yield loss.',
        'plant_parts_attacked': [PlantPart.LEAF],
        'crop_stages_affected': [CropStage.VEGETATIVE],
        'damage_types': [Damage.SAP_LOSS],
        'damage_effects': [DamageEffect.YIELD_LOSS],
        'control_actions': [Control.CHEMICAL_INSECTICIDES, Control.BIOPESTICIDES],
        'control_methods_general': [ControlMethod.CHEMICAL, ControlMethod.BIOLOGICAL]
    },
    
    'Whitefly': {
        'common_name': 'Whitefly',
        'scientific_name': 'Bemisia tabaci',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Feeds on maize leaves and transmits viruses.',
        'damage_summary': 'Sap loss, virus transmission, reduced yield.',
        'plant_parts_attacked': [PlantPart.LEAF],
        'crop_stages_affected': [CropStage.VEGETATIVE],
        'damage_types': [Damage.SAP_LOSS, Damage.VIRUS_TRANSMISSION],
        'damage_effects': [DamageEffect.YIELD_LOSS],
        'control_actions': [Control.BIOPESTICIDES, Control.NATURAL_ENEMIES],
        'control_methods_general': [ControlMethod.BIOLOGICAL]
    },
    
    'Grasshopper': {
        'common_name': 'Grasshopper',
        'scientific_name': 'Acrididae spp.',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Feeds on maize leaves, sometimes causing defoliation.',
        'damage_summary': 'Defoliation and reduced photosynthesis.',
        'plant_parts_attacked': [PlantPart.LEAF],
        'crop_stages_affected': [CropStage.VEGETATIVE],
        'damage_types': [Damage.DEFOLIATION],
        'damage_effects': [DamageEffect.REDUCED_PHOTOSYNTHESIS, DamageEffect.YIELD_LOSS],
        'control_actions': [Control.CHEMICAL_INSECTICIDES, Control.HAND_PICKING],
        'control_methods_general': [ControlMethod.CHEMICAL, ControlMethod.MECHANICAL]
    },
    
    'Locust': {
        'common_name': 'Locust',
        'scientific_name': 'Locusta migratoria',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Feeds on maize leaves in swarms.',
        'damage_summary': 'Severe defoliation, reduced yield.',
        'plant_parts_attacked': [PlantPart.LEAF],
        'crop_stages_affected': [CropStage.VEGETATIVE, CropStage.REPRODUCTIVE],
        'damage_types': [Damage.DEFOLIATION],
        'damage_effects': [DamageEffect.REDUCED_PHOTOSYNTHESIS, DamageEffect.YIELD_LOSS],
        'control_actions': [Control.CHEMICAL_INSECTICIDES],
        'control_methods_general': [ControlMethod.CHEMICAL]
    },
    
    'Rootworm': {
        'common_name': 'Rootworm',
        'scientific_name': 'Diabrotica spp.',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Larvae feed on roots, weakening plants.',
        'damage_summary': 'Root damage, plant death, yield reduction.',
        'plant_parts_attacked': [PlantPart.ROOT],
        'crop_stages_affected': [CropStage.VEGETATIVE],
        'damage_types': [Damage.ROOT_DAMAGE],
        'damage_effects': [DamageEffect.REDUCED_NUTRIENT_UPTAKE, DamageEffect.PLANT_DEATH],
        'control_actions': [Control.CROP_ROTATION, Control.RESISTANT_VARIETIES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.INTEGRATED]
    },
    
    'NematodePest': {
        'common_name': 'Root-knot Nematode',
        'scientific_name': 'Meloidogyne spp.',
        'pest_class': PestCategory.FIELD_PEST,
        'pest_type_info': PestType.NEMATODE,
        'description': 'Root-knot nematodes damage maize roots.',
        'damage_summary': 'Root damage, stunted growth, yield loss.',
        'plant_parts_attacked': [PlantPart.ROOT],
        'crop_stages_affected': [CropStage.VEGETATIVE],
        'damage_types': [Damage.ROOT_DAMAGE],
        'damage_effects': [DamageEffect.REDUCED_NUTRIENT_UPTAKE, DamageEffect.PLANT_DEATH],
        'control_actions': [Control.CROP_ROTATION, Control.RESISTANT_VARIETIES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.INTEGRATED]
    },
    
    'MaizeWeevil': {
        'common_name': 'Maize Weevil',
        'scientific_name': 'Sitophilus zeamais',
        'pest_class': PestCategory.STORAGE_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Infests stored maize grains causing weight loss.',
        'damage_summary': 'Grain loss, reduced quality, post-harvest losses.',
        'plant_parts_attacked': [PlantPart.GRAIN],
        'crop_stages_affected': [CropStage.STORAGE],
        'damage_types': [Damage.GRAIN_LOSS],
        'damage_effects': [DamageEffect.YIELD_LOSS],
        'control_actions': [Control.FIELD_SANITATION],
        'control_methods_general': [ControlMethod.CULTURAL]
    },
    
    'LargerGrainBorer': {
        'common_name': 'Larger Grain Borer',
        'scientific_name': 'Prostephanus truncatus',
        'pest_class': PestCategory.STORAGE_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Infests stored maize grains, tunneling kernels.',
        'damage_summary': 'Grain loss, reduced quality, post-harvest losses.',
        'plant_parts_attacked': [PlantPart.GRAIN],
        'crop_stages_affected': [CropStage.STORAGE],
        'damage_types': [Damage.GRAIN_LOSS],
        'damage_effects': [DamageEffect.YIELD_LOSS],
        'control_actions': [Control.FIELD_SANITATION, Control.CHEMICAL_INSECTICIDES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.CHEMICAL]
    },
    
    'AngoumoisGrainMoth': {
        'common_name': 'Angoumois Grain Moth',
        'scientific_name': 'Sitotroga cerealella',
        'pest_class': PestCategory.STORAGE_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Infests stored maize grains; larvae feed inside kernels.',
        'damage_summary': 'Grain loss, quality deterioration.',
        'plant_parts_attacked': [PlantPart.GRAIN],
        'crop_stages_affected': [CropStage.STORAGE],
        'damage_types': [Damage.QUALITY_LOSS],
        'damage_effects': [DamageEffect.QUALITY_DETERIORATION],
        'control_actions': [Control.FIELD_SANITATION],
        'control_methods_general': [ControlMethod.CULTURAL]
    },
    
    'FlourBeetle': {
        'common_name': 'Flour Beetle',
        'scientific_name': 'Tribolium spp.',
        'pest_class': PestCategory.STORAGE_PEST,
        'pest_type_info': PestType.INSECT,
        'description': 'Attacks stored maize grains and flour products.',
        'damage_summary': 'Grain loss, quality deterioration.',
        'plant_parts_attacked': [PlantPart.GRAIN],
        'crop_stages_affected': [CropStage.STORAGE],
        'damage_types': [Damage.QUALITY_LOSS],
        'damage_effects': [DamageEffect.QUALITY_DETERIORATION],
        'control_actions': [Control.FIELD_SANITATION, Control.CHEMICAL_INSECTICIDES],
        'control_methods_general': [ControlMethod.CULTURAL, ControlMethod.CHEMICAL]
    },
    
    'Rodent': {
        'common_name': 'Rodent',
        'scientific_name': 'Rattus rattus',
        'pest_class': PestCategory.VERTEBRATE_PEST,
        'pest_type_info': PestType.VERTEBRATE,
        'description': 'Feeds on stored and field maize grains.',
        'damage_summary': 'Grain loss, reduced yield.',
        'plant_parts_attacked': [PlantPart.GRAIN],
        'crop_stages_affected': [CropStage.STORAGE],
        'damage_types': [Damage.GRAIN_LOSS],
        'damage_effects': [DamageEffect.YIELD_LOSS],
        'control_actions': [Control.FIELD_SANITATION],
        'control_methods_general': [ControlMethod.CULTURAL]
    },
    
    'Bird': {
        'common_name': 'Quelea Bird',
        'scientific_name': 'Quelea quelea',
        'pest_class': PestCategory.VERTEBRATE_PEST,
        'pest_type_info': PestType.VERTEBRATE,
        'description': 'Feeds on maize grains in the field and storage.',
        'damage_summary': 'Grain loss, yield reduction.',
        'plant_parts_attacked': [PlantPart.COB, PlantPart.GRAIN],
        'crop_stages_affected': [CropStage.REPRODUCTIVE, CropStage.STORAGE],
        'damage_types': [Damage.GRAIN_LOSS],
        'damage_effects': [DamageEffect.YIELD_LOSS],
        'control_actions': [Control.FIELD_SANITATION],
        'control_methods_general': [ControlMethod.CULTURAL]
    }
}


# ===== QUERY FUNCTIONS =====
# Corresponds to query functions in maize_pests.v

def get_pests_by_plant_part(plant_part: PlantPart) -> List[str]:
    """Returns list of pests that attack a specific plant part"""
    return [
        name for name, profile in PEST_PROFILES.items()
        if plant_part in profile['plant_parts_attacked']
    ]


def get_pests_by_crop_stage(crop_stage: CropStage) -> List[str]:
    """Returns list of pests active at a specific crop stage"""
    return [
        name for name, profile in PEST_PROFILES.items()
        if crop_stage in profile['crop_stages_affected']
    ]


def get_pests_by_damage_effect(damage_effect: DamageEffect) -> List[str]:
    """Returns list of pests causing a specific damage effect"""
    return [
        name for name, profile in PEST_PROFILES.items()
        if damage_effect in profile['damage_effects']
    ]


def get_pests_by_category(category: PestCategory) -> List[str]:
    """Returns list of pests in a specific category"""
    return [
        name for name, profile in PEST_PROFILES.items()
        if profile['pest_class'] == category
    ]


def get_pest_profile(pest_name: str) -> Dict:
    """Returns complete profile for a specific pest"""
    return PEST_PROFILES.get(pest_name, None)


# ===== MAIN (for testing) =====

if __name__ == "__main__":
    print("=== Maize Pest Knowledge Base ===\n")
    
    print(f"Total pests in database: {len(PEST_PROFILES)}\n")
    
    print("Field Pests:")
    field_pests = get_pests_by_category(PestCategory.FIELD_PEST)
    print(f"  Count: {len(field_pests)}")
    print(f"  Examples: {', '.join(field_pests[:5])}\n")
    
    print("Storage Pests:")
    storage_pests = get_pests_by_category(PestCategory.STORAGE_PEST)
    print(f"  Count: {len(storage_pests)}")
    print(f"  Examples: {', '.join(storage_pests)}\n")
    
    print("Pests attacking leaves:")
    leaf_pests = get_pests_by_plant_part(PlantPart.LEAF)
    print(f"  {', '.join(leaf_pests)}\n")
    
    print("Pests causing yield loss:")