import React from 'react';
import Select from 'react-select';
import {getStatesByCountryId, getAllCountries, getStatesByCountryName} from '../../services'

export default function CountryStateReactSelect() {
    return (
        <div>
            <Select 
            // value={selectedOption}
            // onChange={this.handleChange}
            options={getAllCountries()}
            />
        </div>
    )
}
