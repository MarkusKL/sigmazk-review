FROM nixos/nix
RUN mkdir -p ~/.config/nix
COPY .devcontainer/nix.conf /mnt/nix.conf
RUN mv /mnt/nix.conf ~/.config/nix/nix.conf

COPY shell.nix default.nix /mnt/
WORKDIR /mnt
RUN nix-shell
COPY . /mnt/
ENTRYPOINT ["nix-shell"]
