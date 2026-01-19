# ================================
# pest_profiles_data.py
# Complete maize pest profiles for Streamlit
# ================================

pest_profiles = {
    "FallArmyworm": {
        "common_name": "FallArmyworm",
        "scientific_name": "Spodoptera frugiperda",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["ReducedPhotosynthesis", "YieldLoss"],
        "plant_parts_attacked": ["Leaf", "Whorl", "Cob"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["ChemicalInsecticides", "NaturalEnemies", "PushPullSystem"],
        "control_methods_general": ["Chemical", "Biological", "Cultural"]
    },
    "AfricanArmyworm": {
        "common_name": "AfricanArmyworm",
        "scientific_name": "Spodoptera exempta",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["ReducedPhotosynthesis", "YieldLoss"],
        "plant_parts_attacked": ["Leaf"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["ChemicalInsecticides", "NaturalEnemies"],
        "control_methods_general": ["Chemical", "Biological"]
    },
    "MaizeStalkBorer": {
        "common_name": "MaizeStalkBorer",
        "scientific_name": "Busseola fusca",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss", "LodgingEffect"],
        "plant_parts_attacked": ["Stem"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["CropRotation"],
        "control_methods_general": ["Cultural"]
    },
    "SpottedStemBorer": {
        "common_name": "SpottedStemBorer",
        "scientific_name": "Chilo partellus",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss", "LodgingEffect"],
        "plant_parts_attacked": ["Stem"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["CropRotation"],
        "control_methods_general": ["Cultural"]
    },
    "PinkStemBorer": {
        "common_name": "PinkStemBorer",
        "scientific_name": "Sesamia calamistis",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss", "LodgingEffect"],
        "plant_parts_attacked": ["Stem"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["CropRotation"],
        "control_methods_general": ["Cultural"]
    },
    "CornEarworm": {
        "common_name": "CornEarworm",
        "scientific_name": "Helicoverpa zea",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Cob"],
        "crop_stages_affected": ["Reproductive"],
        "control_actions": ["ChemicalInsecticides", "NaturalEnemies"],
        "control_methods_general": ["Chemical", "Biological"]
    },
    "Cutworm": {
        "common_name": "Cutworm",
        "scientific_name": "Agrotis spp.",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Stem"],
        "crop_stages_affected": ["Seedling"],
        "control_actions": ["ChemicalInsecticides", "FieldSanitation"],
        "control_methods_general": ["Chemical", "Cultural"]
    },
    "Wireworm": {
        "common_name": "Wireworm",
        "scientific_name": "Elateridae spp.",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["ReducedNutrientUptake", "PlantDeath"],
        "plant_parts_attacked": ["Root"],
        "crop_stages_affected": ["Seed"],
        "control_actions": ["ChemicalInsecticides"],
        "control_methods_general": ["Chemical"]
    },
    "WhiteGrub": {
        "common_name": "WhiteGrub",
        "scientific_name": "Phyllophaga spp.",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["ReducedNutrientUptake", "PlantDeath"],
        "plant_parts_attacked": ["Root"],
        "crop_stages_affected": ["Seedling", "Vegetative"],
        "control_actions": ["ChemicalInsecticides"],
        "control_methods_general": ["Chemical"]
    },
    "Termite": {
        "common_name": "Termite",
        "scientific_name": "Macrotermes spp.",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["ReducedNutrientUptake", "PlantDeath"],
        "plant_parts_attacked": ["Root"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["FieldSanitation", "ChemicalInsecticides"],
        "control_methods_general": ["Cultural", "Chemical"]
    },
    "ShootFly": {
        "common_name": "ShootFly",
        "scientific_name": "Atherigona soccata",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["PlantDeath"],
        "plant_parts_attacked": ["Whorl"],
        "crop_stages_affected": ["Vegetative"],
        "control_actions": ["ResistantVarieties", "FieldSanitation"],
        "control_methods_general": ["Integrated", "Cultural"]
    },
    "Aphid": {
        "common_name": "Aphid",
        "scientific_name": "Rhopalosiphum maidis",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Leaf"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["NaturalEnemies", "Biopesticides"],
        "control_methods_general": ["Biological"]
    },
    "Leafhopper": {
        "common_name": "Leafhopper",
        "scientific_name": "Cicadulina spp.",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Leaf"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["NaturalEnemies"],
        "control_methods_general": ["Biological"]
    },
    "Thrips": {
        "common_name": "Thrips",
        "scientific_name": "Thrips tabaci",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Leaf"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["ChemicalInsecticides", "Biopesticides"],
        "control_methods_general": ["Chemical", "Biological"]
    },
    "Whitefly": {
        "common_name": "Whitefly",
        "scientific_name": "Bemisia tabaci",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Leaf"],
        "crop_stages_affected": ["Vegetative", "Reproductive"],
        "control_actions": ["NaturalEnemies", "Biopesticides"],
        "control_methods_general": ["Biological"]
    },
    "Grasshopper": {
        "common_name": "Grasshopper",
        "scientific_name": "Acrididae spp.",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["ReducedPhotosynthesis", "YieldLoss"],
        "plant_parts_attacked": ["Leaf"],
        "crop_stages_affected": ["Vegetative"],
        "control_actions": ["HandPicking", "ChemicalInsecticides"],
        "control_methods_general": ["Mechanical", "Chemical"]
    },
    "Locust": {
        "common_name": "Locust",
        "scientific_name": "Locusta migratoria",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["ReducedPhotosynthesis", "YieldLoss"],
        "plant_parts_attacked": ["Leaf"],
        "crop_stages_affected": ["Vegetative"],
        "control_actions": ["ChemicalInsecticides", "NaturalEnemies"],
        "control_methods_general": ["Chemical", "Biological"]
    },
    "Rootworm": {
        "common_name": "Rootworm",
        "scientific_name": "Diabrotica spp.",
        "type": "Insect",
        "category": "FieldPest",
        "damage_effects": ["ReducedNutrientUptake", "PlantDeath"],
        "plant_parts_attacked": ["Root"],
        "crop_stages_affected": ["Vegetative"],
        "control_actions": ["ChemicalInsecticides", "CropRotation"],
        "control_methods_general": ["Chemical", "Cultural"]
    },
    "NematodePest": {
        "common_name": "NematodePest",
        "scientific_name": "Meloidogyne spp.",
        "type": "Nematode",
        "category": "FieldPest",
        "damage_effects": ["ReducedNutrientUptake", "PlantDeath"],
        "plant_parts_attacked": ["Root"],
        "crop_stages_affected": ["Seedling", "Vegetative"],
        "control_actions": ["CropRotation", "Biopesticides"],
        "control_methods_general": ["Cultural", "Biological"]
    },
    "MaizeWeevil": {
        "common_name": "MaizeWeevil",
        "scientific_name": "Sitophilus zeamais",
        "type": "Insect",
        "category": "StoragePest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Grain"],
        "crop_stages_affected": ["Storage"],
        "control_actions": ["FieldSanitation", "ChemicalInsecticides"],
        "control_methods_general": ["Cultural", "Chemical"]
    },
    "LargerGrainBorer": {
        "common_name": "LargerGrainBorer",
        "scientific_name": "Prostephanus truncatus",
        "type": "Insect",
        "category": "StoragePest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Grain"],
        "crop_stages_affected": ["Storage"],
        "control_actions": ["FieldSanitation", "ChemicalInsecticides"],
        "control_methods_general": ["Cultural", "Chemical"]
    },
    "AngoumoisGrainMoth": {
        "common_name": "AngoumoisGrainMoth",
        "scientific_name": "Sitotroga cerealella",
        "type": "Insect",
        "category": "StoragePest",
        "damage_effects": ["QualityDeterioration"],
        "plant_parts_attacked": ["Grain"],
        "crop_stages_affected": ["Storage"],
        "control_actions": ["ChemicalInsecticides", "NaturalEnemies"],
        "control_methods_general": ["Chemical", "Biological"]
    },
    "FlourBeetle": {
        "common_name": "FlourBeetle",
        "scientific_name": "Tribolium spp.",
        "type": "Insect",
        "category": "StoragePest",
        "damage_effects": ["QualityDeterioration"],
        "plant_parts_attacked": ["Grain"],
        "crop_stages_affected": ["Storage"],
        "control_actions": ["ChemicalInsecticides"],
        "control_methods_general": ["Chemical"]
    },
    "Rodent": {
        "common_name": "Rodent",
        "scientific_name": "Rattus rattus",
        "type": "Vertebrate",
        "category": "VertebratePest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Grain"],
        "crop_stages_affected": ["Storage"],
        "control_actions": ["HandPicking", "TrapSetting"],
        "control_methods_general": ["Mechanical"]
    },
    "Bird": {
        "common_name": "Bird",
        "scientific_name": "Quelea quelea",
        "type": "Vertebrate",
        "category": "VertebratePest",
        "damage_effects": ["YieldLoss"],
        "plant_parts_attacked": ["Cob", "Grain"],
        "crop_stages_affected": ["Reproductive", "Storage"],
        "control_actions": ["Scarecrows", "Netting"],
        "control_methods_general": ["Mechanical"]
    }
}
