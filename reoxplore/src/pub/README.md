## Add new channels

If you want to add a new type of channel, you can upload a file with your channel's drawing function here.

What you need to do:

- create a `yourchannelname.js` file in `/src/pub/channels` folder
  - name the file with the same name as the channel's name (i.e. `sync.js`)
- create a function with the same name, like this:
  - `export function yourchannelname(p5, startNode, endNode, arrowSize) {...}`
  - choose how the channel is going to look like, there are some functions avaliable:
    - line: draws a line between startNode and endNode; how to use:
      ```js
      import line from "./shapes/line";

      export function yourchannelname(p5, startNode, endNode, arrowSize) {
        line(p5, startNode, endNode); // draws a solid line
        // or
        line(p5, startNode, endNode, true); // parameter isDashed is true, so draws a dashed line
      }
      ```
    - triangle: draws a triangle near startNode or endNode; how to use:
      ```js
      import line from "./shapes/triangle";

      export function yourchannelname(p5, startNode, endNode, arrowSize) {
        triangle(p5, startNode, endNode, arrowSize); // draws a triangle in the endNode pointing to endNode
        triangle(p5, startNode, endNode, arrowSize, "start"); // draws a triangle in the startNode  pointing to endNode
        triangle(p5, startNode, endNode, arrowSize, "end", "normal", true); // draws a triangle in the endNode pointing to startNode
        triangle(p5, startNode, endNode, arrowSize, "end", "big", true); // draws a big triangle in the endNode pointing to startNode
      }
      ```
    - center: draws specific symbols between startNode and endNode; how to use:
      ```js
      import center from "./symbolsPosition/center";

      export function yourchannelname(p5, startNode, endNode, arrowSize) {
        center(p5, startNode, endNode, ["rectangle"]); // draws a rectangle like in fifo
        center(p5, startNode, endNode, ["triangle"], { isTriangleBig: true }); // draws a big triangle like in transform
        center(p5, startNode, endNode, ["zigzag"]); // draws a zigzag like in filter
        center(p5, startNode, endNode, ["circle"]); // draws a circle like in timer
        center(p5, startNode, endNode, ["circle", "circle"]); // draws two circles like in timeddelay
        center(p5, startNode, endNode, ["line", "line"]); // draws two perpendicular lines like in asyncdrain
        center(p5, startNode, endNode, ["triangle", "circle"], { isTriangleBig: true }); // draws a big triangle and a circle like in timedtransformer
      }
      ```
- export the channel function in `/src/pub/index.js` file so they can be used in the project, like this:
  ```
  export * from "./channels/yourchannelname";
  ```
- congratulations, you added a new channel!
