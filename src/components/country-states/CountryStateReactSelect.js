import React, {useState} from 'react';
import Select from 'react-select';
import {getStatesByCountryId, getAllCountries, getStatesByCountryName} from '../../services'

let selectedCountry = null; 

export  function CountryReactSelect(props) {
    // const [countryStates, setCountryState] = useState([]);

    const handleChange = (selectedOption) => {
        selectedCountry = selectedOption.id;
    }
    
    return (
        <div>
            <Select 
            // value={selectedOption}
            onChange={handleChange}
            {...props}
            options={getAllCountries()}
            />
        </div>
    )
}


export function StateReactSelect() {
    const handleChange = () => {
        console.log('doing nothing')
    }

    return(
        <div>
        <Select 
        // value={selectedOption}
        onChange={handleChange}
        
        options={getStatesByCountryId(selectedCountry)}
        />
    </div>
)
    
}