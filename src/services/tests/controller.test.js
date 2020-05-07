import {getAllCountries, getStatesByCountryId, getStatesByCountryName} from '../index'
import { getAllStates } from '../controller';

test('it returns a list of countries as an array ', () => {
    let result = getAllCountries();
    expect(result).toBeInstanceOf(Array);
})

test('It returns a list of states as an array', () => {
    let result = getStatesByCountryId(2);
    expect(result).toBeInstanceOf(Array);
});

test ('It returns a list of states from the country name as an array ', () => {
    let result = getStatesByCountryName('Nigeria');
    expect(result).toBeInstanceOf(Array);
})

test ('It returns a complete list of countries', () => {
    let result = getAllCountries();
    expect(result.length).toBe(246);
})

test (' It returns a complete list of states ', () => {
    let result = getAllStates();
    expect(result.length).toBe(4091);
})