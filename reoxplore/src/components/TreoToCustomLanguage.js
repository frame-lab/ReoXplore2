import React from "react";
import makeRequest from "../utils/makeRequest";

class TreoToCustomLanguage extends React.Component {
  constructor(props) {
    super(props);
    this.state = { resultTitle: "", resultCode: "", resultError: "" };
    this.handleClick = this.handleClick.bind(this);
  }

  async handleClick(treo, path, title) {
    if (!treo) {
      this.setState({ resultError: "Error. Treo is empty." });
      return;
    }
    const treoData = new TextEncoder().encode(
      JSON.stringify({
        content: treo,
      })
    );
    const response = await makeRequest(treoData, path);
    if (response.status === 200)
      this.setState({
        resultCode: response.data,
        resultTitle: title,
        resultError: "",
      });
    else
      this.setState({
        resultError: "Error. Please verify if treo is correct.",
      });
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
            "nuXmv compact"
          )}
          {this.renderButton(
            "Generate nuXmv components code",
            "/nuXmv/components",
            "nuXmv components"
          )}
          {this.renderButton(
            "Generate Coq model",
            "/coq/model",
            "Coq model"
          )}
        </div>
        {this.state.resultError ? (
          <p className="error-msg">{this.state.resultError}</p>
        ) : (
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
        )}
      </div>
    );
  }
}

export default TreoToCustomLanguage;
