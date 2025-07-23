# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This is **Mathlib4**, the mathematics library for Lean 4. It contains extensive formalized mathematics ranging from basic algebra to advanced topics in analysis, algebraic geometry, category theory, and more. The project is a community-maintained library that provides both mathematical definitions/theorems and programming infrastructure.

## Core Development Commands

### Building and Testing
- `lake exe cache get` - Download precompiled `.olean` files (run this first to avoid slow builds)
- `lake build` - Build the entire mathlib library  
- `lake test` - Build and run all tests
- `lake build Mathlib.Import.Path` - Build a specific file (e.g., `lake build Mathlib.Algebra.Group.Defs`)
- `lake exe mk_all` - Update the main import files (`Mathlib.lean`, `Archive.lean`, etc.) after adding new files

### Cache Management
- `lake exe cache get` - Get cached build files
- `lake exe cache get!` - Force re-download cached files
- `lake clean` or `rm -rf .lake` - Clean build artifacts if something goes wrong

### Linting and Style
- `lake exe lint-style` - Run text-based style linters
- Various linters are automatically enforced during builds (see `mathlibOnlyLinters` in `lakefile.lean`)

### Development Tools
- `lake exe shake` - Check files for unnecessary imports
- `lake exe autolabel [PR_NUMBER]` - Add topic labels to PRs (requires `gh` CLI)
- `lake exe pole` - Query build times and calculate longest pole for current commit
- `lake exe unused module_1 module_n` - Analyze unused transitive imports

## Architecture and Code Organization

### Main Library Structure
- **`Mathlib/`** - Core mathematics library organized by topic:
  - `Algebra/` - Basic algebraic structures (groups, rings, fields) and advanced algebra
  - `Analysis/` - Real/complex analysis, functional analysis, calculus
  - `CategoryTheory/` - Category theory and related constructions
  - `Combinatorics/` - Combinatorial mathematics and graph theory
  - `Data/` - Basic data types and structures
  - `FieldTheory/` - Field theory, Galois theory, algebraic closures
  - `Geometry/` - Geometric structures and manifolds
  - `LinearAlgebra/` - Linear algebra, vector spaces, matrices
  - `Logic/` - Logical foundations and encodability
  - `NumberTheory/` - Number theory, modular forms, arithmetic functions
  - `Order/` - Order theory and lattices
  - `RingTheory/` - Commutative algebra and ring theory
  - `SetTheory/` - Set theory, cardinals, ordinals
  - `Topology/` - General topology and topological algebra

### Supporting Libraries
- **`Archive/`** - Formalizations that don't fit elsewhere in mathlib (competition problems, standalone results)
- **`Counterexamples/`** - Mathematical constructions that serve as counterexamples
- **`Tactic/`** - Lean tactics and metaprogramming utilities
- **`Cache/`** - Caching infrastructure for build artifacts
- **`MathlibTest/`** - Tests for tactics and library functionality

### Key Principles
- **Algebraic Hierarchy**: Basic algebra follows a dependency order: `Notation` → `Group` → `GroupWithZero` → `Ring` → `Field`
- **Import Dependencies**: Earlier folders should not import from later ones in the hierarchy
- **Naming Conventions**: Follow [mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
- **Style Guide**: Adhere to the [mathlib style guide](https://leanprover-community.github.io/contribute/style.html)

## Lean 4 Toolchain
- Current version: `leanprover/lean4:v4.21.0-rc3` (see `lean-toolchain`)
- Dependencies managed via Lake (see `lakefile.lean` and `lake-manifest.json`)
- Key dependencies: Batteries, Aesop, Qq, ProofWidgets, ImportGraph

## Testing and Quality Assurance
- Extensive automated testing via CI/CD
- Style linters enforce coding standards
- Bors integration for merge management
- Import graph analysis to detect circular dependencies
- Cache system for fast CI builds

## Documentation
- API documentation generated automatically from source files
- Module-level documentation in many files explains mathematical concepts
- Extensive example usage in `Archive/` and `Counterexamples/`