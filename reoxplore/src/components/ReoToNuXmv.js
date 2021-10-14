import React from "react";
import makeRequest from "../utils/makeRequest";
class ReoToNuXmv extends React.Component {
  constructor(props) {
    super(props);
    this.state = { resultCode: "" };
    this.handleClick = this.handleClick.bind(this);
  }

  async handleClick(treo, path) {
    const treoData = new TextEncoder().encode(
      JSON.stringify({
        content: treo,
      })
    );
    const response = await makeRequest(treoData, path);
    if (response.status == 200) this.setState({ resultCode: response.data });
    else
      this.setState({ resultCode: "Error. Please verify if treo is correct." });
    console.log(response);
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
          <button
            onClick={(e) => {
              this.handleClick(this.props.treo, "/nuXmv/components", e);
            }}
          >
            Generate nuXmv components code
          </button>
        </div>
        <div className="result-container">
          {this.state.resultCode && (
            <textarea
              readOnly
              cols="80"
              rows="20"
              value={this.state.resultCode}
            ></textarea>
          )}
        </div>
      </div>
    );
  }
}

export default ReoToNuXmv;
