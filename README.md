# Database Design Toolkit (dbdtool)

A Prolog-based logic engine designed to automate and verify Relational Database Design processes, including Functional Dependency analysis, Key discovery, and Normalization.

## 🚀 Overview
Building on the logic patterns used in our **Wumpus World** project, the `dbdtool` library provides a robust environment for students to practice database normalization. It automates complex mathematical tasks such as finding Minimal Covers and performing BCNF decompositions.

## 🛠 Installation & Setup
1. **Prerequisites**: Ensure [SWI-Prolog](https://www.swi-prolog.org/) is installed on your system (Windows/macOS/Linux).
2. **Download**: Clone this repository or download the `dbdtool.qlf` file.
3. **Environment**: We recommend using **VS Code** with the *Prolog* extension for the best experience.

## 📖 Quick Start
To begin practicing, create a new Prolog file (e.g., `exercise.pl`) in the same directory and load the library:

```prolog
:- [dbdtool].

% Example: Checking the Normal Form
run_test :-
    R = [a, b, c],
    F = [ [[a], [b]], [[b], [c]] ],
    normalF(R, F).

:- initialization(run_test).
