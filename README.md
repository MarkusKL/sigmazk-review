# SigmaZK

This is a standard Rocq project, which depends primarily on SSProve.
There are four options for how to install dependencies and compile the project.
After following one of the installation methods, the code files can be compiled by running
the command `make` (the `run-*.sh` scripts includes this command).
The file `compile.txt` shows the expected output of a successful compilation.

* **codespace:** (~7 min. run) To use a GitHub codespace, press the green "<> Code" button, press the "Codespaces" tab, press the "+" button. All project files are compiled as part of the initial setup and the output should be visible in a terminal.
  **NB:** Currently, Firefox seems only to partially support the VSCode browser environment.
* **opam:** (~40 min. run) Run `./run-opam.sh`, or manually:
  
    For an opam based installation we suggest
    running the commands
    ```
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam pin add coq-ssprove https://github.com/SSProve/ssprove.git#9b14e90
    ```
    to install dependencies. Then run `make`.
* **nix:** (~30 min. run, ~6 min. with [math-comp cache](https://github.com/rocq-community/coq-nix-toolbox#local-setup-once-per-user-and-computer), see `.devcontainer/nix.conf`) Run `./run-nix.sh`, or manually:
  
    For a nix based installation we suggest using the provided `shell.nix`
    by running `nix-shell` to enter an environment equipped with the required packages.
    Finally, run `make` inside the shell.
* **docker:** (~7 min. run) Run `./run-docker.sh`, or manually:
  
    For a docker based installation we suggest using the provided `Dockerfile`
    to build an image with the required packages installed. Run
    ```
    docker build -t review-sigmazk .
    ```
    to build the image. Run
    ```
    docker run --rm -it review-sigmazk
    ```
    to enter the development environment.
    Finally, run `make` inside the container.

The codespace and docker setups utilize the math-comp [math-comp cache](https://github.com/rocq-community/coq-nix-toolbox#local-setup-once-per-user-and-computer) cache to avoid building dependencies such as math-comp, math-comp-analysis and SSProve.

See the "Artifacts" appendix in the paper for additional information.
