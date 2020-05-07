import {getAllCountries, getStatesByCountryId, getStatesByCountryName} from '../index'

test('it returns a list of countries as an array ', () => {
    let result = getAllCountries();
    expect(result).toBeInstanceOf(Array);
})