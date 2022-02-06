# ReoXplore2

Graphical editor to create Reo circuits that translate the visual model to Treo code (and vice versa) and integrate with [CACoq](https://github.com/frame-lab/CACoq) and [Reo2nuXmv](https://github.com/frame-lab/Reo2nuXmv) compilers.

[Click here](https://frame-lab.github.io/ReoXplore2/) to see the light version with the Reo editor and the translation to Treo.

To use all the compilers, run the project locally:
- install [Node.js and npm](https://nodejs.org/en/)
- install gcc compiler
- install [Coq](https://coq.inria.fr/download)
- clone this repository: `git clone https://github.com/frame-lab/ReoXplore2`
- go to repository folder: `cd ReoXplore2`
- compile files and install packages: `make`
- run server: `node server.js`
- open another terminal and run the frontend: `cd reoxplore && npm run start`
- see the interface at [localhost:3000/ReoXplore2](localhost:3000/ReoXplore2)

The avaiable channels are the Reo canonical channels and three hybrid channels (timer, timeddelay and timedtransformer). If you want to add a new channel, read these [instructions](https://github.com/frame-lab/ReoXplore2/tree/main/reoxplore/src/pub#readme).
