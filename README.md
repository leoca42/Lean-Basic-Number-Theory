# basicnumbertheory

A Lean 4 project for basic number theory. This was mostly to familiarize myself with using Lean in VS Code and building dependencies to the Mathlib library.

Main.lean contains a few definitions and (incomplete) proofs I did to get familiar with Lean syntax

Everything else is infrastructure.

## About Mathlib

**Mathlib** is Lean's comprehensive mathematics library, containing formalized definitions, theorems, and proofs across algebra, analysis, number theory, topology, and more. Think of it as Lean's equivalent to Python's numpy + scipy + sympy combined - a massive mathematical foundation you can build upon.

In this project, Mathlib provides:
- Number theory definitions and theorems
- Algebraic structures (rings, groups, fields)
- Parity functions (`Nat.even`, `Nat.odd`)
- Thousands of proven mathematical results ready to use

## Project Setup

### Initial Setup (First Time Only)

Run these commands in the project directory:

```powershell
# Update and download dependencies
lake update

# Download precompiled Mathlib (saves 1-2 hours of compilation!)
lake exe cache get

# Build your project
lake build
```

**Expected time**: 5-10 minutes depending on internet speed.

### After Setup

Once configured, the project is ready to use. You only need to repeat the setup if:
- You haven't worked on the project in a while and Mathlib updated
- You add new dependencies to `lakefile.toml`
- You encounter import errors

## Project Configuration Files

### `lakefile.toml`
The project configuration file (like Python's `requirements.txt`). Defines:
- Project metadata (name, version)
- **Dependencies**: Which external libraries to use (Mathlib, etc.)
- Build settings and compilation options

**Example dependency declaration**:
```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

### `lake-manifest.json`
The lockfile (like Python's `poetry.lock`). Auto-generated and tracks:
- Exact versions/commits of all dependencies
- Dependency resolution tree
- **Don't edit manually** - updated by `lake update`

**Purpose**: Ensures everyone working on the project uses the exact same Mathlib version for reproducibility.

### The Build Process

1. **`lake update`**: Reads `lakefile.toml`, resolves dependencies, updates `lake-manifest.json`, downloads packages to `.lake/packages/`
2. **`lake exe cache get`**: Downloads precompiled Mathlib binaries (~1-2 GB) instead of compiling from source
3. **`lake build`**: Compiles your project code (fast since Mathlib is already compiled)

## Using Mathlib

Import specific modules as needed:

```lean
import Mathlib.Algebra.Ring.Parity  -- For Nat.even, Nat.odd
import Mathlib.Data.Nat.Prime       -- For prime number functions

#check Nat.even 10  -- Check type of function
```

Browse available modules at [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/).

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
