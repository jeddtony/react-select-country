import countries from './countries';
import states from './states';

export const getAllCountries = () => countries;

// This is just for testing purpose only, to be sure that the states are complete
export const getAllStates = () => states;

export const getStatesByCountryId = (countryId) => {
    let statesForCountry = states.filter(state => String(state.country_id) === String(countryId));
    return statesForCountry;
}

export const getStatesByCountryName = (countryName) => {
    let countryId = getCountryNameFromId(countryName);
    return getStatesByCountryId(countryId);
}

const getCountryNameFromId = (countryName) =>{
    let countryMatch = countries.filter(country => String(country.name) === String(countryName));
    return countryMatch[0];
}