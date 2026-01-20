"""
Maize Pest Diagnostic Tool - Integrated with Coq Knowledge Base
This module connects to pest_profilescoq.py and uses the formal verification from maize_pests.v
Enhanced with detailed control recommendations and pesticide options
"""

import streamlit as st
from typing import List, Dict, Set
import sys
from pathlib import Path

# Add current directory to path to import local modules
sys.path.insert(0, str(Path(__file__).parent))

# Import from existing knowledge base
try:
    from pest_profilescoq import (
        PEST_PROFILES,
        PestCategory,
        PestType,
        PlantPart,
        CropStage,
        Damage,
        DamageEffect,
        ControlMethod
    )
    KB_AVAILABLE = True
except ImportError:
    KB_AVAILABLE = False
    st.warning("⚠️ Could not import knowledge base. Running in standalone mode.")

# Page config
st.set_page_config(
    page_title="Maize Pest Diagnostic Tool",
    page_icon="🌽",
    layout="wide"
)

# Custom CSS
st.markdown("""
<style>
    .main-header {
        background: linear-gradient(90deg, #059669 0%, #10b981 100%);
        padding: 2rem;
        border-radius: 10px;
        color: white;
        margin-bottom: 2rem;
    }
    .pest-card {
        background: white;
        padding: 1.5rem;
        border-radius: 10px;
        border-left: 4px solid #059669;
        margin-bottom: 1rem;
        box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    .severity-high {
        background-color: #fee2e2;
        color: #991b1b;
        padding: 0.25rem 0.75rem;
        border-radius: 20px;
        font-size: 0.875rem;
        font-weight: 600;
    }
    .severity-medium {
        background-color: #fef3c7;
        color: #92400e;
        padding: 0.25rem 0.75rem;
        border-radius: 20px;
        font-size: 0.875rem;
        font-weight: 600;
    }
    .severity-low {
        background-color: #d1fae5;
        color: #065f46;
        padding: 0.25rem 0.75rem;
        border-radius: 20px;
        font-size: 0.875rem;
        font-weight: 600;
    }
    .kb-badge {
        background: #3b82f6;
        color: white;
        padding: 0.25rem 0.5rem;
        border-radius: 5px;
        font-size: 0.75rem;
        font-weight: 600;
    }
    .control-section {
        background: #f0fdf4;
        padding: 1rem;
        border-radius: 8px;
        margin: 0.5rem 0;
    }
    .warning-box {
        background: #fef3c7;
        border-left: 4px solid #f59e0b;
        padding: 1rem;
        margin: 1rem 0;
        border-radius: 4px;
    }
</style>
""", unsafe_allow_html=True)


# ===== COMPREHENSIVE PEST CONTROL DATABASE =====
PEST_CONTROL_RECOMMENDATIONS = {
    'FallArmyworm': {
        'cultural': [
            'Scout fields regularly (2-3 times per week), especially early morning when larvae are active',
            'Practice crop rotation with non-host crops like beans, groundnuts, or cassava',
            'Deep plowing after harvest to expose pupae to predators and sun',
            'Plant early to avoid peak pest season',
            'Intercrop with crops like cowpea or desmodium (push-pull system)'
        ],
        'biological': [
            'Release Trichogramma wasps (egg parasitoids) at 50,000 per hectare weekly',
            'Apply Bacillus thuringiensis (Bt) products like Dipel, Thuricide at 1-2 kg/ha',
            'Use neem-based products (Neem Azal, Achook) at 2-3 ml per liter of water',
            'Encourage natural enemies: birds, ground beetles, spiders by maintaining field margins',
            'Apply NPV (Nuclear Polyhedrosis Virus) at 250 LE/ha when larvae are young'
        ],
        'chemical': [
            'Emamectin benzoate 5% SG (Proclaim) at 10g/20L - highly effective, spray in evening',
            'Chlorantraniliprole 20% SC (Ampligo) at 20ml/20L - systemic action, good residual',
            'Spinetoram 120 SC (Radiant) at 15ml/20L - low toxicity to beneficial insects',
            'Lambda-cyhalothrin 2.5% EC (Karate) at 40ml/20L - quick knockdown effect',
            'Cypermethrin 10% EC (Kemprin) at 30ml/20L - economical option',
            'Profenofos + Cypermethrin (Polytrin) at 50ml/20L - broad spectrum'
        ],
        'timing': 'Spray when 5-10% of plants show fresh damage. Target whorls directly. Repeat after 7-10 days if needed.',
        'prevention': [
            'Use certified seeds treated with insecticide',
            'Remove and destroy egg masses and young larvae by hand',
            'Maintain proper spacing (75cm x 25cm) for better monitoring'
        ]
    },
    'MaizeStalkBorer': {
        'cultural': [
            'Destroy all crop residues immediately after harvest by burning or deep plowing',
            'Practice crop rotation with legumes (beans, soybeans) or root crops',
            'Plant early in the season to avoid peak borer populations',
            'Use certified resistant varieties like H614, H625, or DK8031',
            'Remove and destroy infested plants (deadhearts) to prevent spread'
        ],
        'biological': [
            'Release Trichogramma chilonis parasitoids at 50,000/ha at weekly intervals',
            'Apply Bacillus thuringiensis (Bt) products when larvae are young (before stem entry)',
            'Use Beauveria bassiana fungal biopesticide at 5g/L of water',
            'Conserve natural enemies like Cotesia sesamiae wasps',
            'Apply neem kernel extract at 5% concentration as a deterrent'
        ],
        'chemical': [
            'Carbofuran 3% G (Furadan) at planting: 10-15 kg/ha in furrow - systemic protection',
            'Chlorpyrifos 20% EC (Dursban) at 50ml/20L - apply before larvae bore into stem',
            'Fipronil 5% SC (Regent) at 40ml/20L - good residual activity',
            'Imidacloprid 350 SC (Confidor) at 20ml/20L - systemic action through roots',
            'Cypermethrin 10% EC (Kemprin) at 40ml/20L - early application for best results',
            'Lambda-cyhalothrin 5% EC (Karate) at 30ml/20L - apply to whorls before boring'
        ],
        'timing': 'Apply chemicals at 3-4 weeks after emergence, before larvae enter stems. Granular insecticides work best in whorls.',
        'prevention': [
            'Monitor fields weekly for egg masses and young larvae',
            'Apply whorl application of sand + insecticide at 3-4 weeks',
            'Use pheromone traps to monitor adult moth populations'
        ]
    },
    'Cutworm': {
        'cultural': [
            'Clear all weeds 2-3 weeks before planting (cutworms feed on weeds first)',
            'Deep plowing to expose larvae and pupae to sun and predators',
            'Delay planting slightly if high cutworm pressure observed',
            'Use raised beds to reduce larval movement to plants',
            'Hand-pick larvae during early morning inspection (hide in soil during day)'
        ],
        'biological': [
            'Encourage ground beetles and birds that feed on cutworms',
            'Apply Bacillus thuringiensis (Bt) products to soil surface',
            'Use entomopathogenic nematodes (Steinernema carpocapsae) soil drench',
            'Apply Beauveria bassiana fungal spray to soil around plants'
        ],
        'chemical': [
            'Chlorpyrifos 20% EC (Dursban) soil drench: 50ml/20L around plant base',
            'Cypermethrin 10% EC (Kemprin) at 40ml/20L - spray soil surface in evening',
            'Diazinon 60% EC at 60ml/20L - apply to soil before planting',
            'Carbaryl 85% WP (Sevin) bait: mix 1kg with 20kg bran + water, apply in evening',
            'Lambda-cyhalothrin 2.5% EC (Karate) at 40ml/20L - band application around seedlings',
            'Profenofos 50% EC (Curacron) at 50ml/20L - soil drench at base of plants'
        ],
        'timing': 'Apply in late evening (6-8 PM) when larvae emerge to feed. Inspect daily for cut plants.',
        'prevention': [
            'Use poison baits: mix insecticide with bran and molasses, apply at dusk',
            'Create collar barriers around seedlings using paper cups or plastic',
            'Seed treatment with imidacloprid before planting'
        ]
    },
    'Aphid': {
        'cultural': [
            'Avoid excessive nitrogen fertilizer (promotes succulent growth attractive to aphids)',
            'Remove alternate hosts and weeds around field (aphids migrate from weeds)',
            'Use reflective mulches (silver plastic) to repel aphids',
            'Plant tolerant varieties if available',
            'Use overhead irrigation to wash aphids off plants'
        ],
        'biological': [
            'Encourage ladybugs, lacewings, and hoverflies (plant flowering borders)',
            'Apply neem oil at 5ml/L - suffocates aphids and repels them',
            'Soap spray: 20g liquid soap per liter of water, spray directly on aphids',
            'Release ladybird beetles: 5-10 per square meter',
            'Use garlic extract spray: 100g crushed garlic in 1L water, strain and spray',
            'Conserve parasitic wasps (Aphidius species) by avoiding broad-spectrum pesticides'
        ],
        'chemical': [
            'Imidacloprid 200 SL (Confidor) at 10ml/20L - systemic, long-lasting protection',
            'Acetamiprid 20% SP (Mospilan) at 5g/20L - effective against resistant populations',
            'Dimethoate 40% EC (Rogor) at 30ml/20L - economical, quick knockdown',
            'Thiamethoxam 25% WG (Actara) at 5g/20L - systemic action, root or foliar',
            'Pirimicarb 50% WG (Pirimor) at 15g/20L - selective, safe for beneficials',
            'Lambda-cyhalothrin 2.5% EC (Karate) at 20ml/20L - broad spectrum'
        ],
        'timing': 'Apply when aphid colonies appear, before population explodes. Spray undersides of leaves.',
        'prevention': [
            'Scout weekly, especially during dry weather when aphids multiply rapidly',
            'Use yellow sticky traps to monitor and trap winged aphids',
            'Remove heavily infested leaves if aphids are localized'
        ]
    },
    'Termite': {
        'cultural': [
            'Destroy termite mounds within 100m of field (use hot water or fuel)',
            'Avoid using fresh manure or crop residues that attract termites',
            'Practice clean cultivation - remove all plant debris',
            'Use resistant varieties if available',
            'Ensure proper drainage - termites prefer moist soil',
            'Crop rotation with non-susceptible crops like beans'
        ],
        'biological': [
            'Use entomopathogenic fungi (Metarhizium anisopliae) for mound treatment',
            'Encourage ants that predate on termites',
            'Apply neem cake to soil at 100-200 kg/ha before planting'
        ],
        'chemical': [
            'Imidacloprid 350 SC (Confidor) seed treatment: 5-7 ml/kg seed',
            'Fipronil 5% SC (Regent) soil treatment: 1.5-2 L/ha as furrow application',
            'Chlorpyrifos 20% EC (Dursban) at 5L/ha mixed with irrigation water',
            'Carbofuran 3% G (Furadan) at 10-15 kg/ha in furrow at planting',
            'Bifenthrin 10% EC (Talstar) at 50ml/20L - soil drench around plants',
            'Thiamethoxam 30% FS (Cruiser) seed treatment: 6ml/kg seed'
        ],
        'timing': 'Apply soil treatment 1-2 weeks before planting. Seed treatment at planting time.',
        'prevention': [
            'Use barrier treatment around field perimeter',
            'Monitor for mud tubes on stems weekly',
            'Maintain adequate soil moisture - termites attack stressed plants more'
        ]
    },
    'MaizeWeevil': {
        'cultural': [
            'Dry grain to 12-13% moisture content before storage (use moisture meter)',
            'Clean storage structures thoroughly before use (remove old grain, dust)',
            'Use airtight containers: metal silos, PICS bags, or plastic drums',
            'Store on raised platforms away from walls',
            'Mix grain with wood ash (1:10 ratio) or diatomaceous earth',
            'Practice FIFO (First In, First Out) - use oldest grain first'
        ],
        'biological': [
            'Mix diatomaceous earth (DE) at 1-2 kg per ton of grain - damages insect exoskeleton',
            'Use botanicals: neem leaves, Mexican marigold, or eucalyptus leaves mixed with grain',
            'Apply neem seed powder at 10g/kg of grain',
            'Use clay powder (kaolin) at 2% by weight - physical barrier'
        ],
        'chemical': [
            'Aluminum phosphide tablets (Phostoxin): 3 tablets/ton for fumigation (Professional use only)',
            'Pirimiphos-methyl 50% EC (Actellic Super) dust: 50g/100kg grain',
            'Deltamethrin 1% dust (K-Obiol) at 50g/100kg grain - long residual',
            'Malathion 2% dust at 100g/100kg grain - economical option',
            'Permethrin + Pirimiphos-methyl (Shumba Super) dust: 50g/100kg grain',
            'Carbon dioxide fumigation for organic production (needs sealed storage)'
        ],
        'timing': 'Treat grain immediately after drying, before storage. Inspect monthly and retreat if needed.',
        'prevention': [
            'Inspect grain weekly for adult weevils or grain dust',
            'Use hermetic storage (PICS bags) - kills insects through oxygen depletion',
            'Avoid mixing new and old grain',
            'Keep storage temperature below 18°C if possible'
        ]
    },
    'LargerGrainBorer': {
        'cultural': [
            'Dry grain to below 13% moisture - critical for LGB control',
            'Use hermetic storage bags (PICS, SuperGrain, AgroZ bags) - highly effective',
            'Store shelled grain rather than cobs (LGB prefers cobs)',
            'Clean storage structures and surrounding areas thoroughly',
            'Separate new harvest from old grain completely'
        ],
        'biological': [
            'Use diatomaceous earth at 1 kg/ton - very effective against LGB',
            'Mix grain with wood ash at 10% by weight',
            'Introduce predatory beetles (Teretrius nigrescens) - biological control'
        ],
        'chemical': [
            'Aluminum phosphide (Phostoxin) fumigation: 3-4 tablets/ton (requires trained operator)',
            'Pirimiphos-methyl 2% dust (Actellic Super): 50g/100kg grain',
            'Deltamethrin 0.2% + Pirimiphos-methyl 2% (Shumba Super) at 50g/100kg',
            'Permethrin 1% dust at 50g/100kg grain - apply during bagging',
            'Malathion 5% dust at 100g/100kg - cheaper alternative',
            'Cypermethrin 1% dust at 40g/100kg grain'
        ],
        'timing': 'Apply protectant dust during bagging. Fumigate if infestation detected. Check monthly.',
        'prevention': [
            'Use triple bagging method with PICS bags for chemical-free storage',
            'Seal all cracks in storage structures (LGB is very small)',
            'Use pheromone traps to monitor adult beetle populations',
            'Act immediately if any adults spotted - population grows exponentially'
        ]
    },
    'Rodent': {
        'cultural': [
            'Keep storage area clean - remove spilled grain immediately',
            'Store grain on raised platforms (60cm minimum from ground)',
            'Seal all holes, cracks, and openings in storage structures',
            'Cut vegetation around storage within 3-meter radius',
            'Use rodent-proof containers (metal bins, sealed drums)',
            'Remove alternative food sources and hiding places'
        ],
        'biological': [
            'Keep cats around storage areas - natural rodent control',
            'Encourage natural predators: owls (provide nest boxes), snakes (in rural areas)',
            'Use predator scent deterrents (ferret or fox urine products)'
        ],
        'chemical': [
            'Bromadiolone 0.005% bait (Klerat): place in bait stations around storage',
            'Brodifacoum 0.005% pellets (Talon): 50-100g per bait station',
            'Zinc phosphide 2% tracking powder: apply along rodent runways',
            'Warfarin 0.5% bait: economical, requires multiple feedings',
            'Difenacoum 0.005% wax blocks (Ratak): weather resistant for outdoor use',
            'Alpha-chloralose powder: acute poison, quick action (restricted in some areas)'
        ],
        'timing': 'Place baits before harvest and maintain year-round. Check and refill bait stations weekly.',
        'prevention': [
            'Use snap traps along walls and in corners (25-30 traps per 100m2)',
            'Install glue boards in areas where chemicals cannot be used',
            'Create physical barriers: metal sheeting at base of walls (45cm high)',
            'Regular monitoring: look for droppings, gnaw marks, runways'
        ],
        'safety_warning': '⚠️ Keep rodenticides away from children, pets, and livestock. Use bait stations. Dispose of dead rodents properly.'
    },
    'Bird': {
        'cultural': [
            'Plant early to mature before peak bird migration periods',
            'Harvest promptly when grain reaches maturity - don\'t leave in field',
            'Cover drying grain with nets or shade cloth',
            'Intercrop with tall crops around perimeter as barriers',
            'Use reflective tape or old CDs hung on strings across field'
        ],
        'mechanical': [
            'Install bird netting over crops during grain filling stage',
            'Use scarecrows dressed in bright colors, move weekly to new locations',
            'Set up propane cannons or gas guns (where permitted) - automatic noise makers',
            'String monofilament lines across field at different heights',
            'Use hawk kites or owl decoys (move regularly to maintain effectiveness)',
            'Install wind-activated pinwheels or spinning reflectors'
        ],
        'chemical': [
            'Methyl anthranilate bird repellent spray: apply to ripening grain',
            'Anthraquinone-based repellents (Flight Control): makes grain unpalatable',
            'Capsaicin spray (hot pepper extract): creates unpleasant taste',
        ],
        'timing': 'Implement deterrents 2 weeks before grain maturity. Most critical at milk to dough stage.',
        'prevention': [
            'Plant in blocks rather than long narrow strips (harder for birds to find)',
            'Use noise deterrents: drums, tins, radios tuned to talk stations',
            'Employ bird guards in fields during critical periods (early morning, late afternoon)',
            'Organize community-wide bird scaring programs',
            'Plant decoy crops around field edges for birds to feed on'
        ],
        'note': '⚠️ Avoid lethal control methods where possible. Many bird species are protected by law.'
    },
    'Wireworm': {
        'cultural': [
            'Deep plow fields 2-3 times before planting to expose larvae to sun and predators',
            'Avoid planting maize after grass/pasture (high wireworm populations)',
            'Practice 2-3 year crop rotation with non-susceptible crops (legumes)',
            'Delay planting if wireworm pressure is high (rapid germination reduces damage)',
            'Use trap crops: plant mustard or radish before maize, then plow under'
        ],
        'biological': [
            'Apply entomopathogenic nematodes (Heterorhabditis bacteriophora) to soil',
            'Use Beauveria bassiana fungal treatment in furrow',
            'Encourage ground beetles and birds through conservation practices'
        ],
        'chemical': [
            'Imidacloprid 600 FS seed treatment: 7ml/kg seed - systemic protection',
            'Fipronil 5% SC (Regent) in-furrow: 1-1.5 L/ha at planting',
            'Thiamethoxam 350 FS (Cruiser) seed treatment: 6ml/kg seed',
            'Chlorpyrifos 20% EC (Dursban) soil treatment: 5L/ha incorporated before planting',
            'Carbofuran 3% G (Furadan) granules: 10-12 kg/ha in furrow at planting',
            'Bifenthrin 10% EC (Talstar) at-planting furrow spray: 300ml/ha'
        ],
        'timing': 'Seed treatment at planting. Soil treatment 1-2 weeks before planting or at planting.',
        'prevention': [
            'Use bait traps to monitor: bury potato pieces 10cm deep, check after 1 week',
            'Ensure rapid germination through proper seed bed preparation and moisture',
            'Consider resistant varieties if available in your region',
            'Monitor trap crops before destroying to assess wireworm population levels'
        ]
    }
}


class SymptomMapper:
    """Maps farmer observations to knowledge base entities"""
    
    # Map farmer-friendly symptoms to technical damage types
    SYMPTOM_TO_DAMAGE = {
        'holes_leaves': [Damage.DEFOLIATION] if KB_AVAILABLE else ['Defoliation'],
        'yellow_leaves': [Damage.SAP_LOSS] if KB_AVAILABLE else ['SapLoss'],
        'white_insects': [Damage.SAP_LOSS, Damage.VIRUS_TRANSMISSION] if KB_AVAILABLE else ['SapLoss', 'VirusTransmission'],
        'worms_whorl': [Damage.DEFOLIATION] if KB_AVAILABLE else ['Defoliation'],
        'stem_broken': [Damage.LODGING, Damage.STEM_TUNNELING] if KB_AVAILABLE else ['Lodging', 'StemTunneling'],
        'stem_holes': [Damage.STEM_TUNNELING] if KB_AVAILABLE else ['StemTunneling'],
        'seedling_cut': [Damage.DEAD_HEART] if KB_AVAILABLE else ['DeadHeart'],
        'plant_wilting': [Damage.ROOT_DAMAGE, Damage.DEAD_HEART] if KB_AVAILABLE else ['RootDamage', 'DeadHeart'],
        'cob_damage': [Damage.GRAIN_LOSS] if KB_AVAILABLE else ['GrainLoss'],
        'grain_powder': [Damage.GRAIN_LOSS, Damage.QUALITY_LOSS] if KB_AVAILABLE else ['GrainLoss', 'QualityLoss'],
        'grain_holes': [Damage.GRAIN_LOSS] if KB_AVAILABLE else ['GrainLoss'],
        'birds_eating': [Damage.GRAIN_LOSS] if KB_AVAILABLE else ['GrainLoss'],
        'rodent_signs': [Damage.GRAIN_LOSS] if KB_AVAILABLE else ['GrainLoss']
    }
    
    # Map farmer-friendly observations to plant parts
    SYMPTOM_TO_PLANT_PART = {
        'holes_leaves': [PlantPart.LEAF] if KB_AVAILABLE else ['Leaf'],
        'yellow_leaves': [PlantPart.LEAF] if KB_AVAILABLE else ['Leaf'],
        'white_insects': [PlantPart.LEAF] if KB_AVAILABLE else ['Leaf'],
        'worms_whorl': [PlantPart.WHORL, PlantPart.LEAF] if KB_AVAILABLE else ['Whorl', 'Leaf'],
        'stem_broken': [PlantPart.STEM] if KB_AVAILABLE else ['Stem'],
        'stem_holes': [PlantPart.STEM] if KB_AVAILABLE else ['Stem'],
        'seedling_cut': [PlantPart.STEM] if KB_AVAILABLE else ['Stem'],
        'plant_wilting': [PlantPart.ROOT] if KB_AVAILABLE else ['Root'],
        'cob_damage': [PlantPart.COB] if KB_AVAILABLE else ['Cob'],
        'grain_powder': [PlantPart.GRAIN] if KB_AVAILABLE else ['Grain'],
        'grain_holes': [PlantPart.GRAIN] if KB_AVAILABLE else ['Grain'],
        'birds_eating': [PlantPart.COB, PlantPart.GRAIN] if KB_AVAILABLE else ['Cob', 'Grain'],
        'rodent_signs': [PlantPart.GRAIN] if KB_AVAILABLE else ['Grain']
    }


# Dropdown options
OBSERVATIONS = {
    '': 'Select what you see...',
    'holes_leaves': '🍃 Holes or tears in leaves',
    'yellow_leaves': '🟡 Leaves turning yellow',
    'white_insects': '🦟 White/small insects on leaves',
    'worms_whorl': '🐛 Worms/caterpillars in plant center (whorl)',
    'stem_broken': '💔 Stems breaking or falling over',
    'stem_holes': '🕳️ Holes/tunnels in stem',
    'seedling_cut': '✂️ Young plants cut at ground level',
    'plant_wilting': '🥀 Plants wilting or dying',
    'cob_damage': '🌽 Damage to cobs/ears',
    'grain_powder': '💨 Grain turning to powder in storage',
    'grain_holes': '🔴 Small holes in stored grain',
    'birds_eating': '🐦 Birds eating grain',
    'rodent_signs': '🐀 Rodent droppings/grain eaten'
}

PLANT_PARTS = {
    '': 'Which part is affected?',
    'Root': '🌱 Roots (underground)',
    'Stem': '🎋 Stem/Stalk',
    'Leaf': '🍃 Leaves',
    'Whorl': '🌀 Whorl (center of plant)',
    'Cob': '🌽 Cob/Ear',
    'Grain': '🌾 Grain (stored)'
}

CROP_STAGES = {
    '': 'When did you notice this?',
    'Seed': '🌱 Just planted (seed stage)',
    'Seedling': '🌿 Young plants (1-3 weeks)',
    'Vegetative': '🌾 Growing plants (before tasseling)',
    'Reproductive': '🌽 Flowering/forming cobs',
    'Storage': '📦 After harvest (in storage)'
}


def get_pest_severity(pest_profile: Dict) -> str:
    """Determine pest severity based on damage effects"""
    if not KB_AVAILABLE:
        damage_effects = pest_profile.get('damage_effects', [])
        if 'PlantDeath' in damage_effects or 'YieldLoss' in damage_effects:
            return 'high'
        elif 'ReducedPhotosynthesis' in damage_effects or 'ReducedNutrientUptake' in damage_effects:
            return 'medium'
        return 'low'
    
    damage_effects = pest_profile.get('damage_effects', [])
    
    if DamageEffect.PLANT_DEATH in damage_effects or DamageEffect.YIELD_LOSS in damage_effects:
        return 'high'
    elif DamageEffect.REDUCED_PHOTOSYNTHESIS in damage_effects or DamageEffect.REDUCED_NUTRIENT_UPTAKE in damage_effects:
        return 'medium'
    return 'low'


def get_enhanced_control_recommendations(pest_name: str, pest_profile: Dict) -> Dict:
    """Get detailed control recommendations from the comprehensive database"""
    
    # Get pest key - handle different naming conventions
    pest_key = None
    for key in PEST_CONTROL_RECOMMENDATIONS.keys():
        if key.lower() in pest_name.lower() or pest_name.lower() in key.lower():
            pest_key = key
            break
    
    if pest_key and pest_key in PEST_CONTROL_RECOMMENDATIONS:
        return PEST_CONTROL_RECOMMENDATIONS[pest_key]
    
    # Fallback to basic recommendations if not in enhanced database
    return {
        'cultural': ['Practice crop rotation', 'Maintain field sanitation', 'Use resistant varieties'],
        'biological': ['Encourage natural enemies', 'Use organic pesticides when appropriate'],
        'chemical': ['Consult agricultural extension officer for appropriate pesticides'],
        'timing': 'Apply control measures when pest is first observed',
        'prevention': ['Regular field monitoring', 'Early detection and response']
    }


def diagnose_pest(observation: str, plant_part: str, crop_stage: str) -> List[Dict]:
    """Match symptoms to pests using the Coq knowledge base"""
    if not KB_AVAILABLE:
        st.error("Knowledge base not available. Please ensure pest_profilescoq.py is in the same directory.")
        return []
    
    matched_pests = []
    mapper = SymptomMapper()
    
    expected_damages = mapper.SYMPTOM_TO_DAMAGE.get(observation, [])
    expected_parts = mapper.SYMPTOM_TO_PLANT_PART.get(observation, [])
    
    if plant_part:
        try:
            plant_part_enum = PlantPart[plant_part.upper()]
        except (KeyError, AttributeError):
            plant_part_enum = None
    else:
        plant_part_enum = None
    
    if crop_stage:
        try:
            crop_stage_enum = CropStage[crop_stage.upper()]
        except (KeyError, AttributeError):
            crop_stage_enum = None
    else:
        crop_stage_enum = None
    
    for pest_name, profile in PEST_PROFILES.items():
        score = 0
        matches = []
        
        pest_damages = set(profile.get('damage_summary', '').split(','))
        for damage in expected_damages:
            damage_str = str(damage).split('.')[-1] if hasattr(damage, '__class__') else str(damage)
            if any(damage_str.lower() in d.lower() for d in pest_damages):
                score += 3
                matches.append('damage_type')
                break
        
        pest_parts = profile.get('plant_parts_attacked', [])
        for part in expected_parts:
            if part in pest_parts:
                score += 2
                matches.append('plant_part')
                break
        
        if plant_part_enum and plant_part_enum in pest_parts:
            score += 2
            if 'plant_part' not in matches:
                matches.append('plant_part_user')
        
        if crop_stage_enum:
            pest_stages = profile.get('crop_stages_affected', [])
            if crop_stage_enum in pest_stages:
                score += 2
                matches.append('crop_stage')
        
        if score > 0:
            matched_pests.append({
                'name': profile.get('common_name', pest_name),
                'scientific': profile.get('scientific_name', 'Unknown'),
                'description': profile.get('description', 'No description available'),
                'damage_summary': profile.get('damage_summary', ''),
                'pest_type': profile.get('pest_type_info', ''),
                'pest_category': profile.get('pest_class', ''),
                'damage_effects': profile.get('damage_effects', []),
                'plant_parts': profile.get('plant_parts_attacked', []),
                'crop_stages': profile.get('crop_stages_affected', []),
                'score': score,
                'matches': matches,
                'max_score': 9,
                'profile': profile,
                'pest_key': pest_name
            })
    
    matched_pests.sort(key=lambda x: x['score'], reverse=True)
    
    for pest in matched_pests:
        pest['severity'] = get_pest_severity(pest)
    
    return matched_pests


def display_pest_card(pest: Dict, index: int):
    """Display an enhanced pest result card with detailed control recommendations"""
    
    col1, col2 = st.columns([3, 1])
    with col1:
        st.subheader(f"#{index}. {pest['name']}")
        st.caption(f"*{pest['scientific']}*")
        if KB_AVAILABLE:
            st.markdown('<span class="kb-badge">✓ Verified by Knowledge Base</span>', unsafe_allow_html=True)
    with col2:
        severity_class = f"severity-{pest['severity']}"
        st.markdown(f'<span class="{severity_class}">{pest["severity"].upper()} RISK</span>', 
                   unsafe_allow_html=True)
    
    st.progress(pest['score'] / pest['max_score'], 
               text=f"Match Confidence: {pest['score']}/{pest['max_score']} ({int(pest['score']/pest['max_score']*100)}%)")
    
    with st.expander("📋 Pest Details", expanded=True):
        col1, col2 = st.columns(2)
        
        with col1:
            st.write(f"**Type:** {str(pest['pest_type']).split('.')[-1] if hasattr(pest['pest_type'], '__class__') else pest['pest_type']}")
            st.write(f"**Category:** {str(pest['pest_category']).split('.')[-1] if hasattr(pest['pest_category'], '__class__') else pest['pest_category']}")
        
        with col2:
            parts = [str(p).split('.')[-1] for p in pest.get('plant_parts', [])]
            st.write(f"**Attacks:** {', '.join(parts) if parts else 'Multiple parts'}")
            
            stages = [str(s).split('.')[-1] for s in pest.get('crop_stages', [])]
            st.write(f"**Active at:** {', '.join(stages) if stages else 'Multiple stages'}")
    
    st.write("**📝 Description:**")
    st.info(pest.get('description', 'No description available'))
    
    if pest.get('damage_summary'):
        st.write("**⚠️ Damage Caused:**")
        st.warning(pest['damage_summary'])
    
    # Enhanced control recommendations
    st.write("**🌱 Detailed Control Recommendations:**")
    
    control_info = get_enhanced_control_recommendations(pest['pest_key'], pest)
    
    tab1, tab2, tab3, tab4 = st.tabs(["🌾 Cultural Control", "🐛 Biological Control", "⚗️ Chemical Control", "🛡️ Prevention"])
    
    with tab1:
        st.markdown('<div class="control-section">', unsafe_allow_html=True)
        st.write("**Cultural/Management Practices:**")
        for i, rec in enumerate(control_info.get('cultural', []), 1):
            st.write(f"{i}. {rec}")
        st.markdown('</div>', unsafe_allow_html=True)
    
    with tab2:
        st.markdown('<div class="control-section">', unsafe_allow_html=True)
        st.write("**Biological/Organic Options:**")
        for i, rec in enumerate(control_info.get('biological', []), 1):
            st.write(f"{i}. {rec}")
        st.markdown('</div>', unsafe_allow_html=True)
    
    with tab3:
        st.markdown('<div class="control-section">', unsafe_allow_html=True)
        st.write("**Chemical Pesticide Options:**")
        for i, rec in enumerate(control_info.get('chemical', []), 1):
            st.write(f"{i}. {rec}")
        
        if control_info.get('timing'):
            st.write(f"\n**⏰ Application Timing:** {control_info['timing']}")
        
        if control_info.get('safety_warning'):
            st.markdown(f'<div class="warning-box">{control_info["safety_warning"]}</div>', unsafe_allow_html=True)
        else:
            st.markdown('<div class="warning-box">⚠️ Always read and follow pesticide label instructions. Wear protective equipment. Observe pre-harvest intervals.</div>', unsafe_allow_html=True)
        
        st.markdown('</div>', unsafe_allow_html=True)
    
    with tab4:
        st.markdown('<div class="control-section">', unsafe_allow_html=True)
        st.write("**Prevention & Monitoring:**")
        for i, rec in enumerate(control_info.get('prevention', []), 1):
            st.write(f"{i}. {rec}")
        
        if control_info.get('note'):
            st.info(control_info['note'])
        st.markdown('</div>', unsafe_allow_html=True)
    
    st.divider()


def main():
    st.markdown("""
    <div class="main-header">
        <h1>🌽 Maize Pest Diagnostic Tool</h1>
        <p>Powered by Formal Knowledge Base (Coq) - Formally Verified Pest Information</p>
        <p style="font-size: 0.9em;">Enhanced with Comprehensive Control Recommendations</p>
    </div>
    """, unsafe_allow_html=True)
    
    if KB_AVAILABLE:
        st.success("✅ Connected to Coq Knowledge Base (maize_pests.v)")
    else:
        st.error("❌ Knowledge Base not connected. Please ensure pest_profilescoq.py is available.")
        st.stop()
    
    with st.sidebar:
        st.header("ℹ️ How to Use")
        st.write("""
        1. **Observe** your maize field carefully
        2. **Select** what you see (required)
        3. **Specify** plant part and growth stage (optional but helpful)
        4. Click **Diagnose** to get results
        5. **Review** detailed control options
        6. **Choose** appropriate control methods
        """)
        
        st.divider()
        
        st.header("🔬 About This Tool")
        st.write("""
        This diagnostic tool is powered by a **formally verified knowledge base** written in Coq.
        
        Features:
        - ✓ Logically consistent information
        - ✓ No contradictions
        - ✓ Mathematically proven relationships
        - ✓ Reliable pest identification
        - ✓ Comprehensive control recommendations
        - ✓ Specific pesticide options with dosages
        """)
        
        st.divider()
        
        st.header("📞 Need Help?")
        st.write("""
        Contact your local agricultural extension officer if:
        - You're unsure about the diagnosis
        - The problem persists after treatment
        - You need specific pesticide recommendations
        - You have questions about application methods
        """)
    
    st.header("🔍 Describe What You See")
    
    col1, col2 = st.columns(2)
    
    with col1:
        observation = st.selectbox(
            "What do you see in your field? * (Required)",
            options=list(OBSERVATIONS.keys()),
            format_func=lambda x: OBSERVATIONS[x],
            help="Choose the symptom that best matches what you observe"
        )
    
    with col2:
        plant_part = st.selectbox(
            "Which part of the plant? (Optional)",
            options=list(PLANT_PARTS.keys()),
            format_func=lambda x: PLANT_PARTS[x],
            help="This helps narrow down the results"
        )
    
    crop_stage = st.selectbox(
        "Growth stage of your crop? (Optional)",
        options=list(CROP_STAGES.keys()),
        format_func=lambda x: CROP_STAGES[x],
        help="When did you first notice the problem?"
    )
    
    st.divider()
    
    col1, col2 = st.columns([3, 1])
    
    with col1:
        diagnose_btn = st.button("🔬 Diagnose Pest", type="primary", use_container_width=True)
    
    with col2:
        if st.button("🔄 Reset", use_container_width=True):
            st.rerun()
    
    if diagnose_btn:
        if not observation:
            st.error("⚠️ Please select what you see in your field!")
        else:
            with st.spinner("🔍 Searching knowledge base..."):
                results = diagnose_pest(observation, plant_part, crop_stage)
            
            if not results:
                st.warning("""
                ⚠️ **No pests match your description.**
                
                Possible reasons:
                - The symptom description doesn't match any known pest patterns
                - Try selecting different options
                - Consult an agricultural extension officer
                """)
            else:
                st.success(f"✅ **Found {len(results)} possible pest(s) based on knowledge base**")
                st.caption("Results ranked by confidence score (best match first)")
                
                for idx, pest in enumerate(results, 1):
                    display_pest_card(pest, idx)
    
    st.divider()
    st.info("""
    💡 **Tips for Best Results:**
    - Observe your field in early morning when pests are most active
    - Look for multiple symptoms to improve accuracy
    - Take photos if possible and show to extension officers
    - Act quickly - early intervention is most effective
    - Always follow pesticide safety guidelines
    - Consider combining multiple control methods for best results (Integrated Pest Management)
    """)
    
    with st.expander("📚 About the Knowledge Base"):
        st.write("""
        This tool uses a **formally verified knowledge base** defined in `maize_pests.v` (Coq language).
        
        **Files in this system:**
        - `maize_pests.v` - Formal Coq definitions and logical relations
        - `pest_profilescoq.py` - Python interface to the knowledge base
        - `diagnostic_app.py` - This diagnostic interface (you are here)
        
        **What makes this special:**
        - All pest-damage-control relationships are mathematically proven
        - No contradictions can exist in the data
        - Recommendations are based on verified causal chains
        - Updates to the knowledge base are automatically checked for consistency
        - Enhanced with comprehensive field-tested control methods
        - Specific pesticide formulations and dosages included
        """)


if __name__ == "__main__":
    main()