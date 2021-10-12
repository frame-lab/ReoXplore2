import React from "react";
const http = require("http");

const options = {
  hostname: "localhost",
  port: 8081,
  path: "/nuXmv/compact",
  method: "POST",
};

async function makeRequest(data) {
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

  async handleClick(treo) {
    console.log("calling Reo2nuXmv");
    const treoData = new TextEncoder().encode(
      JSON.stringify({
        content: treo,
      })
    );
    const nuXmvCode = await makeRequest(treoData);
    this.setState({ nuXmvCode: nuXmvCode });
  }

  render() {
    return (
      <div>
        <button
          onClick={(e) => {
            this.handleClick(this.props.treo, e);
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
