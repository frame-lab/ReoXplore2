import React from "react";
import encodeTextForRequest from "../utils/encodeTextForRequest";
import makeRequest from "../utils/makeRequest";
import parseTreoToHaskellInput from "../utils/parseTreoToHaskellInput";
import DownloadButton from "./DownloadButton";

const isLightVersion = true; // feature flag to publish the interface in github pages; comment this line if you are running the project on your machine

class TreoToCustomLanguage extends React.Component {
  constructor(props) {
    super(props);
    this.state = {
      resultTitle: "",
      resultCode: "",
      resultError: "",
      resultFileName: "",
    };
    this.handleClick = this.handleClick.bind(this);
  }

  async handleClick(treo, path, title, filename) {
    if (!treo) {
      this.setState({ resultError: "Error. Treo is empty." });
      return;
    }
    const treoData = encodeTextForRequest(treo);
    const response = await makeRequest(treoData, path);
    if (response.status === 200)
      this.setState({
        resultCode: response.data,
        resultTitle: title,
        resultError: "",
        resultFileName: filename,
      });
    else
      this.setState({
        resultError: "Error. Please verify if treo is correct.",
      });
  }

  renderButton = (text, path, title, filename) => {
    const treo =
      path === "/haskell/model"
        ? parseTreoToHaskellInput(this.props.treo)
        : this.props.treo;
    return (
      <button
        type="button"
        onClick={(e) => {
          e.preventDefault();
          this.handleClick(treo, path, title, filename, e);
        }}
      >
        {text}
      </button>
    );
  };

  render() {
    return (
      <main className="options-container">
        {isLightVersion ? (
          <p>
            This is a light version.{" "}
            <a href="https://github.com/frame-lab/ReoXplore2">
              See instructions
            </a>{" "}
            for running the project locally to get access to all features.
          </p>
        ) : (
          <div>
            <div>
              {this.renderButton(
                "Generate nuXmv compact code",
                "/nuXmv/compact",
                "nuXmv compact",
                "nuXmvCompact.smv"
              )}
              {this.renderButton(
                "Generate nuXmv components code",
                "/nuXmv/components",
                "nuXmv components",
                "nuXmvComponents.smv"
              )}
              {this.renderButton(
                "Generate Coq model",
                "/coq/model",
                "Coq model",
                "coqModel.v"
              )}
              {this.renderButton(
                "Generate Haskell code",
                "/haskell/model",
                "Haskell code",
                "haskellModel.hs"
              )}
            </div>
            {this.state.resultError ? (
              <p className="error-msg">{this.state.resultError}</p>
            ) : (
              <div className="result-container">
                {this.state.resultCode && (
                  <div>
                    <div className="result-header">
                      <h4>{this.state.resultTitle}</h4>
                      <DownloadButton
                        fileData={this.state.resultCode}
                        fileName={this.state.resultFileName}
                      />
                    </div>
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
        )}
      </main>
    );
  }
}

export default TreoToCustomLanguage;
