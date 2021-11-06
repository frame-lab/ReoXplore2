/** Replace all numbers of treo with a{number} to prepare for haskell compiler input.
 * @param {string} treo
 * @returns the treo with its labels modified
 * i.e. sync(1,2) becomes sync(a1,a2)
 */
export default function parseTreoToHaskellInput(treo) {
  const regex = /(\d+)/g;
  const treoForHaskellInput = treo.replace(regex, "a$1");
  return treoForHaskellInput;
}
