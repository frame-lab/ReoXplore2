export default function getUniqueNodesFromArray(nodes) {
  let uniqueLabels = [];
  let uniqueNodes = [];
  for (let node of nodes) {
    if (!uniqueLabels.includes(node.label)) {
      uniqueNodes.push(node);
      uniqueLabels.push(node.label);
    }
  }
  return uniqueNodes;
}
