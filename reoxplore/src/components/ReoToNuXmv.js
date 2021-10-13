import React from "react";
const http = require("http");

const options = {
  hostname: "localhost",
  port: 8081,
  method: "POST",
};

async function makeRequest(data, path) {
  options["path"] = path;
  return await new Promise((resolve, reject) => {
    const req = http.request(options, (res) => {
      console.log(`statusCode: ${res.statusCode}`);

      res.on("data", (d) => {
        const dataString = new TextDecoder().decode(d);
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

  async handleClick(treo, path) {
    const treoData = new TextEncoder().encode(
      JSON.stringify({
        content: treo,
      })
    );
    const nuXmvCode = await makeRequest(treoData, path);
    // TODO: verify request success
    this.setState({ nuXmvCode: nuXmvCode });
  }

  render() {
    return (
      <div className="options-container">
        <div>
          <button
            onClick={(e) => {
              this.handleClick(this.props.treo, "/nuXmv/compact", e);
            }}
          >
            Generate nuXmv compact code
          </button>
        </div>
        <div className="result-container">
          {this.state.nuXmvCode && (
            <textarea
              readOnly
              cols="80"
              rows="20"
              value={this.state.nuXmvCode}
            ></textarea>
          )}
        </div>
      </div>
    );
  }
}

export default ReoToNuXmv;
