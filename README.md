# ReoXplore2

Graphical editor to create Reo circuits that translate the visual model to Treo code (and vice versa) and integrate with [CACoq](https://github.com/frame-lab/CACoq) and [Reo2nuXmv](https://github.com/frame-lab/Reo2nuXmv) compilers.

[Click here](https://frame-lab.github.io/ReoXplore2/) to see the light version with the Reo editor and the translation to Treo.

To use all the compilers, run the project locally:
- install [Node.js and npm](https://nodejs.org/en/), gcc compiler, make, [Coq](https://coq.inria.fr/download)
    - Debian/Ubuntu based: `sudo apt install git build-essential nodejs npm coq -y` 
        - tested in version:
            - git/jammy-updates,jammy-security,now 1:2.34.1-1ubuntu1.8 amd64
            - build-essential/jammy,now 12.9ubuntu3 amd64
            - gcc version 11.3.0 (Ubuntu 11.3.0-1ubuntu1~22.04) 
            - nodejs/jammy 12.22.9~dfsg-1ubuntu3 amd64
            - npm/jammy,now 8.5.1~ds-1 all
            - coq/jammy 8.15.0+dfsg-2 amd64
    - Arch: `sudo pacman -S git gcc make nodejs-lts-fermium npm coq`
        - suports nodejs 14


- clone this repository: `git clone https://github.com/frame-lab/ReoXplore2`
- go to repository folder: `cd ReoXplore2`
- compile files and install packages: `make`
- run server: `node server.js`
- open another terminal and run the frontend: `cd reoxplore && npm run start`
- see the interface at [localhost:3000/ReoXplore2](localhost:3000/ReoXplore2)

The avaiable channels are the Reo canonical channels and three hybrid channels (timer, timeddelay and timedtransformer). If you want to add a new channel, read these [instructions](https://github.com/frame-lab/ReoXplore2/tree/main/reoxplore/src/pub#readme).

- image---