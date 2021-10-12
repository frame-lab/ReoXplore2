import React from "react";

const http = require("http");

// TODO: get treo and pass it as a parameter for the request
const data = new TextEncoder().encode(
  JSON.stringify({
    content: "sync(1,2)",
  })
);

const options = {
  hostname: "localhost",
  port: 8081,
  path: "/nuXmv/compact",
  method: "POST",
};

async function makeRequest() {
  return await new Promise((resolve, reject) => {
    const req = http.request(options, (res) => {
      console.log(`statusCode: ${res.statusCode}`);

      res.on("data", (d) => {
        let dataString = new TextDecoder().decode(d);
        console.log(dataString);
        resolve(dataString);
      });
    });

    req.on("error", (error) => {
      console.error(error);
      reject(error);
    });

    req.write(data);
    req.end();
  });
}

class ReoToNuXmv extends React.Component {
  constructor(props) {
    super(props);
    this.state = { nuXmvCode: "" };
    this.handleClick = this.handleClick.bind(this);
  }

  async handleClick() {
    console.log("calling Reo2nuXmv");
    let nuXmvCode = await makeRequest();
    this.setState({ nuXmvCode: nuXmvCode });
  }

  render() {
    return (
      <div>
        <button
          onClick={(e) => {
            this.handleClick("", e);
          }}
        >
          Generate nuXmv code
        </button>
        {/* TODO: show nuXmv code */}
      </div>
    );
  }
}

export default ReoToNuXmv;
