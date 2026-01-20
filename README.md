# MaizeKB - Maize Pest Knowledge Base

## Table of Contents
1. [Overview](#overview)
2. [Features](#features)
3. [Installation](#installation)
4. [Project Structure](#project-structure)
5. [Usage](#usage)
6. [Pest Categories](#pest-categories)
7. [Application Components](#application-components)
8. [Development](#development)
9. [Contributing](#contributing)
10. [Troubleshooting](#troubleshooting)

---

## Overview

MaizeKB is a comprehensive knowledge base system designed to help farmers, agronomists, and agricultural professionals identify and manage maize pests. The system provides detailed information about various pests affecting maize crops, including identification features, damage patterns, affected plant parts, and recommended control methods.

### Key Objectives
- Provide accessible pest identification and management information
- Support both field and storage pest management
- Offer interactive diagnostic capabilities
- Enable evidence-based decision making for pest control

---

## Features

### Pest Information Management
- **Detailed Pest Profiles**: Each pest entry includes:
  - Common name and scientific name
  - Pest classification (Insect, Nematode, Vertebrate)
  - Category (Field Pest, Storage Pest, Vertebrate Pest)
  - Comprehensive damage descriptions
  - Plant parts affected
  - Crop growth stages impacted
  - Control recommendations

### Interactive Interface
- User-friendly **Streamlit** web application
- Search and filter functionality
- Multiple search criteria:
  - Pest name (common or scientific)
  - Category (Field, Storage, Vertebrate)
  - Pest type
  - Plant part attacked
  - Crop stage affected
  - Damage effects
  - Control methods

### Diagnostic Capabilities
- Interactive pest diagnosis tool
- Symptom-based pest identification
- Recommended treatment suggestions

---

## Installation

### Prerequisites
- Python 3.7 or higher
- pip (Python package installer)
- Git (for cloning the repository)

### Step-by-Step Installation

1. **Clone the Repository**
   ```bash
   git clone https://github.com/Vonnyblue/MaizeKB.git
   cd MaizeKB
   ```

2. **Create a Virtual Environment** (Recommended)
   ```bash
   # On Windows
   python -m venv venv
   venv\Scripts\activate

   # On macOS/Linux
   python3 -m venv venv
   source venv/bin/activate
   ```

3. **Install Dependencies**
   ```bash
   pip install -r requirements.txt
   ```

4. **Verify Installation**
   ```bash
   python --version
   pip list
   ```

---

## Project Structure

```
MaizeKB/
├── .devcontainer/          # Development container configuration
├── .vscode/                # VS Code settings
├── __pycache__/           # Python cache files
├── diagnostic_app.py       # Main diagnostic application
├── maizeapp.py            # Core application logic
├── pest_profilescoq.py    # Pest profile definitions
├── maize_pests.v          # Formal verification code (Rocq/Coq)
├── requirements.txt       # Python dependencies
├── README.md             # Project README
└── git                   # Git configuration
```

### File Descriptions

- **diagnostic_app.py**: Interactive Streamlit application for pest diagnosis
- **maizeapp.py**: Main application interface and user interaction logic
- **pest_profilescoq.py**: Database of pest profiles with detailed information
- **maize_pests.v**: Formal specification using Rocq Prover (Coq)
- **requirements.txt**: List of required Python packages

---

## Usage

### Running the Application

1. **Start the Streamlit App**
   ```bash
   streamlit run diagnostic_app.py
   ```
   Or alternatively:
   ```bash
   streamlit run maizeapp.py
   ```

2. **Access the Application**
   - Open your web browser
   - Navigate to `http://localhost:8501`
   - The application will load automatically

### Using the Diagnostic Tool

1. **Browse Pest Profiles**
   - View all available pest information
   - Filter by category, type, or other criteria

2. **Search for Specific Pests**
   - Use the search bar to find pests by name
   - Filter results by multiple criteria

3. **Diagnose Pest Problems**
   - Select observed symptoms
   - Identify affected plant parts
   - Review recommended control measures

4. **Get Control Recommendations**
   - View integrated pest management strategies
   - Access chemical and biological control options
   - Review cultural control practices

---

## Pest Categories

### 1. Field Pests
Pests that attack maize crops during the growing season in the field.

**Common Field Pests Include:**
- **Fall Armyworm** (*Spodoptera frugiperda*): Attacks leaves, stems, and developing ears
- **Maize Stalk Borer** (*Busseola fusca*): Bores into stems causing plant wilting
- **Aphids** (Various species): Suck plant sap and transmit viral diseases
- **Cutworms**: Cut young plants at soil level
- **Leaf Miners**: Create tunnels in leaves
- **Thrips**: Damage leaves and transmit diseases

### 2. Storage Pests
Pests that infest harvested maize grain during storage.

**Common Storage Pests Include:**
- **Maize Weevil** (*Sitophilus zeamais*): Primary storage pest causing grain damage
- **Larger Grain Borer** (*Prostephanus truncatus*): Highly destructive storage pest
- **Flour Beetle** (Various species): Infests processed grain products
- **Angoumois Grain Moth**: Larvae develop inside grain kernels
- **Lesser Grain Borer**: Attacks whole grains

### 3. Vertebrate Pests
Birds and mammals that damage maize crops.

**Common Vertebrate Pests Include:**
- **Birds** (*Quelea quelea*): Eat maize seeds and developing grain
- **Rodents** (Rats and mice): Damage seeds, seedlings, and stored grain
- **Monkeys**: Damage ears and plants in some regions

---

## Application Components

### User Interface Features

1. **Navigation Menu**
   - Home/Dashboard
   - Pest Database
   - Diagnostic Tool
   - Control Methods
   - About

2. **Search and Filter Options**
   - Text search by pest name
   - Category filter (Field/Storage/Vertebrate)
   - Type filter (Insect/Nematode/Vertebrate)
   - Plant part filter
   - Crop stage filter
   - Damage effect filter
   - Control method filter

3. **Pest Profile Display**
   - Pest identification details
   - Damage description with images (if available)
   - Lifecycle information
   - Economic impact
   - Management recommendations

### Data Structure

Each pest profile contains:
```python
{
    "common_name": str,
    "scientific_name": str,
    "pest_type": str,  # Insect/Nematode/Vertebrate
    "category": str,   # FieldPest/StoragePest/VertebratePest
    "description": str,
    "damage_summary": str,
    "plant_parts_attacked": list,
    "crop_stages_affected": list,
    "damage_effects": list,
    "control_methods": {
        "cultural": list,
        "chemical": list,
        "biological": list,
        "integrated": list
    }
}
```

---

## Development

### Setting Up Development Environment

1. **VS Code Configuration**
   - The project includes `.vscode` settings for optimal development
   - Recommended extensions will be suggested

2. **Development Container**
   - `.devcontainer` configuration available
   - Ensures consistent development environment

### Code Style and Standards

- Follow PEP 8 guidelines for Python code
- Use meaningful variable and function names
- Add docstrings to functions and classes
- Comment complex logic

### Testing

To add tests to the project:
```bash
# Install pytest
pip install pytest

# Run tests
pytest tests/
```

### Adding New Pests

1. Open `pest_profilescoq.py`
2. Add new pest entry following the existing format
3. Include all required fields
4. Update documentation
5. Test the application

---

## Contributing

We welcome contributions to MaizeKB! Here's how you can help:

### How to Contribute

1. **Fork the Repository**
   - Click the "Fork" button on GitHub
   - Clone your fork locally

2. **Create a Feature Branch**
   ```bash
   git checkout -b feature/your-feature-name
   ```

3. **Make Your Changes**
   - Add new pest profiles
   - Improve documentation
   - Fix bugs
   - Enhance features

4. **Commit Your Changes**
   ```bash
   git add .
   git commit -m "Description of changes"
   ```

5. **Push to Your Fork**
   ```bash
   git push origin feature/your-feature-name
   ```

6. **Create a Pull Request**
   - Go to the original repository
   - Click "New Pull Request"
   - Describe your changes

### Contribution Guidelines

- Ensure code follows project style guidelines
- Test your changes thoroughly
- Update documentation as needed
- Add yourself to contributors list

---

## Troubleshooting

### Common Issues

#### Installation Problems

**Issue**: `pip install` fails
```bash
# Solution: Update pip
python -m pip install --upgrade pip
```

**Issue**: Streamlit not found
```bash
# Solution: Ensure virtual environment is activated
# and streamlit is installed
pip install streamlit
```

#### Application Issues

**Issue**: Application won't start
- Check if port 8501 is already in use
- Try a different port: `streamlit run app.py --server.port 8502`

**Issue**: Missing dependencies
```bash
# Reinstall all dependencies
pip install -r requirements.txt --force-reinstall
```

**Issue**: Import errors
- Ensure you're in the correct directory
- Verify virtual environment is activated
- Check Python version compatibility

### Getting Help

- **GitHub Issues**: Report bugs or request features at [GitHub Issues](https://github.com/Vonnyblue/MaizeKB/issues)
- **Documentation**: Review this documentation
- **Community**: Engage with other users and contributors

---

## Additional Resources

### Related Links
- [Streamlit Documentation](https://docs.streamlit.io)
- [Python Documentation](https://docs.python.org)
- [Integrated Pest Management](https://www.fao.org/agriculture/crops/thematic-sitemap/theme/pests/ipm/en/)

### Pest Management Resources
- FAO Pest Management Guidelines
- Local Agricultural Extension Services
- Crop Protection Associations

---

## License

Please check the repository for license information.

## Acknowledgments

- Contributors to the MaizeKB project
- Agricultural experts who provided pest information
- Open-source community for tools and libraries

---

## Contact

For questions, suggestions, or collaboration opportunities:
- GitHub: [@Vonnyblue](https://github.com/Vonnyblue)
- Repository: [MaizeKB](https://github.com/Vonnyblue/MaizeKB)

---

**Last Updated**: January 2026  
**Version**: 1.0  
**Maintainer**: Vonnyblue