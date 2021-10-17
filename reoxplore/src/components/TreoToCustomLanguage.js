import React from "react";
import makeRequest from "../utils/makeRequest";

class TreoToCustomLanguage extends React.Component {
  constructor(props) {
    super(props);
    this.state = { resultTitle: "", resultCode: "" };
    this.handleClick = this.handleClick.bind(this);
  }

  async handleClick(treo, path, title) {
    if (!treo) {
      this.setState({ resultCode: "Error. Treo is empty." });
      return;
    }
    const treoData = new TextEncoder().encode(
      JSON.stringify({
        content: treo,
      })
    );
    const response = await makeRequest(treoData, path);
    if (response.status === 200)
      this.setState({ resultCode: response.data, resultTitle: title });
    else
      this.setState({ resultCode: "Error. Please verify if treo is correct." });
    console.log(response);
  }

  renderButton = (text, path, title) => {
    return (
      <button
        onClick={(e) => {
          this.handleClick(this.props.treo, path, title, e);
        }}
      >
        {text}
      </button>
    );
  };

  render() {
    return (
      <div className="options-container">
        <div>
          {this.renderButton(
            "Generate nuXmv compact code",
            "/nuXmv/compact",
            "NuXmv Compact"
          )}
          {this.renderButton(
            "Generate nuXmv components code",
            "/nuXmv/components",
            "NuXmv Components"
          )}
        </div>
        <div className="result-container">
          {this.state.resultCode && (
            <div>
              <h4>{this.state.resultTitle}</h4>
              <textarea
                readOnly
                cols="80"
                rows="20"
                value={this.state.resultCode}
              ></textarea>
            </div>
          )}
        </div>
      </div>
    );
  }
}

export default TreoToCustomLanguage;
