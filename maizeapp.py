# =============================
#maizeapp.py
# =============================
import streamlit as st
from pest_profilescoq import pest_profiles

# st.title("Maize Pest Knowledge Base")

# # Sidebar for query type
# query_type = st.sidebar.selectbox(
#     "Select query type",
#     ["By Pest Name", "By Category", "By Pest Type", "By Damage Effect", "By Crop Stage", "By Plant Part"]
# )


# -----------------------------
# Precompute dropdown options
# -----------------------------
all_names = [p["common_name"] for p in pest_profiles.values()]
all_categories = list(set([p["category"] for p in pest_profiles.values()]))
all_types = list(set([p["type"] for p in pest_profiles.values()]))

all_plant_parts = sorted(list({part for p in pest_profiles.values() for part in p["plant_parts_attacked"]}))
all_stages = sorted(list({stage for p in pest_profiles.values() for stage in p["crop_stages_affected"]}))
all_damage_effects = sorted(list({effect for p in pest_profiles.values() for effect in p["damage_effects"]}))
all_control_methods = sorted(list({method for p in pest_profiles.values() for method in p["control_methods_general"]}))

# -----------------------------
# Helper functions
# -----------------------------
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

# Display pest profile nicely
def display_pest_profile(profile):
    st.subheader(profile["common_name"])
    st.write(f"**Scientific Name:** {profile['scientific_name']}")
    st.write(f"**Type:** {profile['type']}")
    st.write(f"**Category:** {profile['category']}")
    st.write(f"**Damage Effects:** {', '.join(profile['damage_effects'])}")
    st.write(f"**Plant Parts Attacked:** {', '.join(profile['plant_parts_attacked'])}")
    st.write(f"**Crop Stages Affected:** {', '.join(profile['crop_stages_affected'])}")
    st.write(f"**Control Actions:** {', '.join(profile['control_actions'])}")
    st.write(f"**Control Methods:** {', '.join(profile['control_methods_general'])}")
    st.markdown("---")

# -----------------------------
# Streamlit App
# -----------------------------
st.title("🌽 Maize Pest Knowledge Base")

# Select query type
query_type = st.selectbox(
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

# Select input dynamically based on query type
query_input = None
if query_type == "Name":
    query_input = st.selectbox("Select Pest Name:", all_names)
elif query_type == "Category":
    query_input = st.selectbox("Select Category:", all_categories)
elif query_type == "Type":
    query_input = st.selectbox("Select Type:", all_types)
elif query_type == "Plant Part Attacked":
    query_input = st.selectbox("Select Plant Part:", all_plant_parts)
elif query_type == "Crop Stage Affected":
    query_input = st.selectbox("Select Crop Stage:", all_stages)
elif query_type == "Damage Effect":
    query_input = st.selectbox("Select Damage Effect:", all_damage_effects)
elif query_type == "Control Method":
    query_input = st.selectbox("Select Control Method:", all_control_methods)

# Execute query
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
