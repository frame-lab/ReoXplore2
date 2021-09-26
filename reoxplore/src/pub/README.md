## Add new channels

If you want to add a new type of channel, you can upload a file with your channel's drawing function here.

What you need to do:

- create a `.js` file in `/channels` folder
- name the file with the same name as the channel's name (i.e. `sync.js`)
- create a function with the same name, like this:
  - `export function yourchannelname(p5, startNode, endNode, arrowSize) {...}`
  - you can try it out first in the [p5 editor](https://editor.p5js.org/) to see how your channel will look like, here is an example of the [sync channel](https://editor.p5js.org/ferreira-mariana/sketches/UYgUC2cWR)
  - copy the code of your channel function from p5 editor and paste in the function you created in the `.js` file
  - write a `p5.` before all p5js functions (i.e. `line(10, 20, 10, 100);` in p5 editor must be `p5.line(10, 20, 10, 100);` here)
- export the channel function in the `index.js` file so they can be used in the project, like this:
  - `export * from "./channels/yourchannelname";`
- congratulations, you added a new channel!
