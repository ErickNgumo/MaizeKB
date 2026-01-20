import streamlit as st
from pest_profilescoq import pest_profiles

# -----------------------------
# App title
# -----------------------------
st.title("Maize Pest Knowledge Base 🌽🐛")

# =====================================================
# PRECOMPUTE OPTIONS (ORIGINAL FUNCTIONALITY)
# =====================================================
all_names = [p["common_name"] for p in pest_profiles.values()]
all_categories = sorted(list(set([p["category"] for p in pest_profiles.values()])))
all_types = sorted(list(set([p["type"] for p in pest_profiles.values()])))
all_plant_parts = sorted(list({part for p in pest_profiles.values() for part in p["plant_parts_attacked"]}))
all_stages = sorted(list({stage for p in pest_profiles.values() for stage in p["crop_stages_affected"]}))
all_damage_effects = sorted(list({effect for p in pest_profiles.values() for effect in p["damage_effects"]}))
all_control_methods = sorted(list({method for p in pest_profiles.values() for method in p["control_methods_general"]}))

# =====================================================
# NEW: SYMPTOM AUTO-SUGGESTION SOURCE
# =====================================================
all_symptoms = all_damage_effects.copy()

# =====================================================
# HELPER SEARCH FUNCTIONS (ORIGINAL)
# =====================================================
def search_by_name(name):
    return pest_profiles.get(name, None)

def search_by_category(category):
    return [p for p in pest_profiles.values() if p["category"] == category]

def search_by_type(pest_type):
    return [p for p in pest_profiles.values() if p["type"] == pest_type]

def search_by_plant_part(part):
    return [p for p in pest_profiles.values() if part in p["plant_parts_attacked"]]

def search_by_crop_stage(stage):
    return [p for p in pest_profiles.values() if stage in p["crop_stages_affected"]]

def search_by_damage_effect(effect):
    return [p for p in pest_profiles.values() if effect in p["damage_effects"]]

def search_by_control_method(method):
    return [p for p in pest_profiles.values() if method in p["control_methods_general"]]

# =====================================================
# NEW: SEARCH BY MULTIPLE SYMPTOMS (KRR INFERENCE)
# =====================================================
def search_by_multiple_symptoms(symptoms):
    results = []
    for pest in pest_profiles.values():
        matched = set(symptoms) & set(pest["damage_effects"])
        if matched:
            pest_copy = pest.copy()
            pest_copy["matched_symptoms"] = list(matched)
            pest_copy["match_score"] = len(matched)
            results.append(pest_copy)
    return sorted(results, key=lambda x: x["match_score"], reverse=True)

# =====================================================
# DISPLAY FUNCTION
# =====================================================
def display_pest_profile(profile):
    st.subheader(profile["common_name"])
    st.write(f"**Scientific Name:** {profile['scientific_name']}")
    st.write(f"**Type:** {profile['type']}")
    st.write(f"**Category:** {profile['category']}")
    st.write(f"**Description:** {profile.get('description', 'No description')}")
    st.write(f"**Damage Summary:** {profile.get('damage_summary', 'No summary')}")
    st.write(f"**Damage Effects:** {', '.join(profile['damage_effects'])}")
    st.write(f"**Plant Parts Attacked:** {', '.join(profile['plant_parts_attacked'])}")
    st.write(f"**Crop Stages Affected:** {', '.join(profile['crop_stages_affected'])}")

    st.markdown("### ✅ Recommended Control Solutions")
    st.write(", ".join(profile["control_actions"]))
    st.write(f"**Control Methods:** {', '.join(profile['control_methods_general'])}")
    st.markdown("---")

# =====================================================
# NEW: SYMPTOM-BASED SEARCH (ADDED FEATURE)
# =====================================================
st.header("🔍 Diagnose by Observed Symptoms")

selected_symptoms = st.multiselect(
    "Start typing observed symptoms:",
    options=all_symptoms,
    help="Auto-suggestions come from the knowledge base"
)

symptom_search = st.button("Search by Symptoms")

if symptom_search:
    if not selected_symptoms:
        st.warning("Please select at least one symptom.")
    else:
        results = search_by_multiple_symptoms(selected_symptoms)

        if results:
            st.success(f"{len(results)} possible pest(s)/disease(s) identified:")

            for profile in results:
                st.caption(
                    f"Matched Symptoms: {', '.join(profile['matched_symptoms'])}"
                )
                display_pest_profile(profile)
        else:
            st.error("No pests or diseases match the selected symptoms.")

# =====================================================
# SIDEBAR (ORIGINAL FUNCTIONALITY PRESERVED)
# =====================================================
st.sidebar.header("🔎 Advanced Search")

query_type = st.sidebar.selectbox(
    "Search pests by:",
    [
        "Name",
        "Category",
        "Type",
        "Plant Part Attacked",
        "Crop Stage Affected",
        "Damage Effect",
        "Control Method"
    ]
)

query_input = None
if query_type == "Name":
    query_input = st.sidebar.selectbox("Select Pest Name:", all_names)
elif query_type == "Category":
    query_input = st.sidebar.selectbox("Select Category:", all_categories)
elif query_type == "Type":
    query_input = st.sidebar.selectbox("Select Type:", all_types)
elif query_type == "Plant Part Attacked":
    query_input = st.sidebar.selectbox("Select Plant Part:", all_plant_parts)
elif query_type == "Crop Stage Affected":
    query_input = st.sidebar.selectbox("Select Crop Stage:", all_stages)
elif query_type == "Damage Effect":
    query_input = st.sidebar.selectbox("Select Damage Effect:", all_damage_effects)
elif query_type == "Control Method":
    query_input = st.sidebar.selectbox("Select Control Method:", all_control_methods)

# =====================================================
# EXECUTE SIDEBAR QUERY (ORIGINAL)
# =====================================================
if query_input:
    results = []

    if query_type == "Name":
        profile = search_by_name(query_input)
        if profile:
            results = [profile]
    elif query_type == "Category":
        results = search_by_category(query_input)
    elif query_type == "Type":
        results = search_by_type(query_input)
    elif query_type == "Plant Part Attacked":
        results = search_by_plant_part(query_input)
    elif query_type == "Crop Stage Affected":
        results = search_by_crop_stage(query_input)
    elif query_type == "Damage Effect":
        results = search_by_damage_effect(query_input)
    elif query_type == "Control Method":
        results = search_by_control_method(query_input)

    if results:
        st.success(f"{len(results)} pest(s) found:")
        for profile in results:
            display_pest_profile(profile)
    else:
        st.warning("No pests found for this query.")
